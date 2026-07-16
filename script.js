/* ════════════════════════════════════════════════════
   2D Grid Map — A* Pathfinding Visualizer
   Grid : COLS(40) × ROWS(20)
   Start: dynamic (default col=2, row=2)
   Walls: ~25%  (Fisher-Yates shuffle)

   Animation pipeline
   ──────────────────
   Click → A*(sync) → [VISITING phase] → [PATHING phase] → DONE
   Right-Click  → Move Start Node
   L-Drag       → Toggle Walls
   Speed Select → 1x / 2x / 5x / Instant
   ════════════════════════════════════════════════════ */

'use strict';

// ════════════════════════════════════════════════════
//  Config
// ════════════════════════════════════════════════════
const COLS       = 40;
const ROWS       = 20;
const WALL_RATIO = 0.25;
const CELL_GAP   = 1;

// 시작점 — 우클릭으로 이동 가능, F5 전까지 세션 유지
let startCol = 2;
let startRow = 2;

// ════════════════════════════════════════════════════
//  Speed Config
// ════════════════════════════════════════════════════
const SPEED_PRESETS = {
  '1':       { visitPerFrame:  4, pathPerFrame: 1, visitFade: 280, pathFade: 180 },
  '2':       { visitPerFrame: 10, pathPerFrame: 2, visitFade: 150, pathFade:  90 },
  '5':       { visitPerFrame: 30, pathPerFrame: 4, visitFade:  70, pathFade:  40 },
  'instant': { visitPerFrame: Infinity, pathPerFrame: Infinity, visitFade: 0, pathFade: 0 },
};

let speedKey = '1';
const getSpeed = () => SPEED_PRESETS[speedKey];

// ════════════════════════════════════════════════════
//  Cell Types
// ════════════════════════════════════════════════════
const CELL = Object.freeze({
  EMPTY:   0,
  WALL:    1,
  START:   2,
  END:     3,
  PATH:    4,
  VISITED: 5,
});

// ════════════════════════════════════════════════════
//  Animation State Machine
// ════════════════════════════════════════════════════
const ANIM = Object.freeze({ IDLE: 0, VISITING: 1, PATHING: 2, DONE: 3 });

let animState   = ANIM.IDLE;
let animFrameId = null;
let visitedSeq  = [];
let pathSeq     = null;
let visitIdx    = 0;
let pathIdx     = 0;
let activeFades = [];

// ════════════════════════════════════════════════════
//  Drag State  (L-Click 드래그 → 벽 토글)
// ════════════════════════════════════════════════════
let isDragging   = false;  // 마우스 누른 상태
let hasDragged   = false;  // 다른 셀로 이동했는지 여부
let dragMode     = null;   // 'add' | 'remove'
let lastDragCell = null;   // 마지막으로 처리한 셀 { col, row }

// ════════════════════════════════════════════════════
//  Grid State
// ════════════════════════════════════════════════════
let grid       = [];
let cellSize   = 20;
let toastTimer = null;

// ════════════════════════════════════════════════════
//  DOM References
// ════════════════════════════════════════════════════
const canvas       = document.getElementById('gridCanvas');
const ctx          = canvas.getContext('2d');
const btnRefresh   = document.getElementById('btn-refresh');
const wallCountEl  = document.getElementById('wall-count');
const footerStatus = document.getElementById('footer-status');
const toast        = document.getElementById('toast');
const speedSelect  = document.getElementById('speed-select');

// ════════════════════════════════════════════════════
//  Colour Map
// ════════════════════════════════════════════════════
const cv = getComputedStyle(document.documentElement);
const COLOR = {
  empty:    cv.getPropertyValue('--cell-empty').trim()    || '#141628',
  emptyAlt: cv.getPropertyValue('--cell-empty-alt').trim()|| '#161930',
  wall:     cv.getPropertyValue('--cell-wall').trim()     || '#1e2042',
  wallFace: cv.getPropertyValue('--cell-wall-face').trim()|| '#4f52a0',
  start:    cv.getPropertyValue('--cell-start').trim()    || '#22d3ee',
  end:      cv.getPropertyValue('--cell-end').trim()      || '#f59e0b',
  path:     cv.getPropertyValue('--cell-path').trim()     || '#84cc16',
  visited:  cv.getPropertyValue('--cell-visited').trim()  || '#2d3494',
  gridLine: cv.getPropertyValue('--cell-grid-line').trim()|| 'rgba(99,102,241,0.09)',
};

// ════════════════════════════════════════════════════
//  Canvas & Grid Init
// ════════════════════════════════════════════════════

function resizeCanvas() {
  const pad  = 32;
  const avW  = canvas.parentElement.clientWidth  - pad;
  const avH  = canvas.parentElement.clientHeight - pad;
  const cell = Math.max(8, Math.min(Math.floor(avW / COLS), Math.floor(avH / ROWS)));
  canvas.width  = cell * COLS + CELL_GAP * (COLS + 1);
  canvas.height = cell * ROWS + CELL_GAP * (ROWS + 1);
  cellSize = cell;
  return cell;
}

/** Fisher-Yates 셔플로 25% 랜덤 장애물 배치 (startCol/startRow는 맵 새로고침에도 유지) */
function initGrid() {
  const wallTarget = Math.round(ROWS * COLS * WALL_RATIO);
  grid = Array.from({ length: ROWS }, () => new Uint8Array(COLS));
  grid[startRow][startCol] = CELL.START;

  const idx = [];
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      if (!(r === startRow && c === startCol)) idx.push(r * COLS + c);

  for (let i = 0; i < wallTarget; i++) {
    const j = i + Math.floor(Math.random() * (idx.length - i));
    [idx[i], idx[j]] = [idx[j], idx[i]];
    grid[Math.floor(idx[i] / COLS)][idx[i] % COLS] = CELL.WALL;
  }
  return wallTarget;
}

/** VISITED · PATH · END 셀을 EMPTY로 되돌린다 */
function clearPathState() {
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++) {
      const t = grid[r][c];
      if (t === CELL.VISITED || t === CELL.PATH || t === CELL.END)
        grid[r][c] = CELL.EMPTY;
    }
}

/** 현재 그리드의 장애물 수 카운트 */
function countWalls() {
  let w = 0;
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      if (grid[r][c] === CELL.WALL) w++;
  return w;
}

// ════════════════════════════════════════════════════
//  A* Algorithm — Manhattan 휴리스틱, 4방향
// ════════════════════════════════════════════════════

function runAStar(sc, sr, ec, er) {
  const h    = (c, r) => Math.abs(c - ec) + Math.abs(r - er);
  const DIRS = [[0, -1], [0, 1], [-1, 0], [1, 0]];
  const key  = (c, r) => r * COLS + c;

  const gScore   = new Float32Array(ROWS * COLS).fill(Infinity);
  const cameFrom = new Int32Array(ROWS * COLS).fill(-1);
  const inOpen   = new Uint8Array(ROWS * COLS);
  const inClosed = new Uint8Array(ROWS * COLS);
  const visited  = [];
  const open     = [];

  const sk = key(sc, sr);
  gScore[sk] = 0;
  open.push({ k: sk, c: sc, r: sr, f: h(sc, sr) });
  inOpen[sk] = 1;

  while (open.length > 0) {
    let mi = 0;
    for (let i = 1; i < open.length; i++)
      if (open[i].f < open[mi].f) mi = i;

    const cur = open[mi];
    open.splice(mi, 1);
    inOpen[cur.k]   = 0;
    inClosed[cur.k] = 1;
    visited.push({ col: cur.c, row: cur.r });

    if (cur.c === ec && cur.r === er) {
      const path = [];
      for (let k = cur.k; k !== -1; k = cameFrom[k])
        path.push({ col: k % COLS, row: Math.floor(k / COLS) });
      return { visitedSeq: visited, pathSeq: path.reverse() };
    }

    for (const [dc, dr] of DIRS) {
      const nc = cur.c + dc, nr = cur.r + dr;
      if (nc < 0 || nc >= COLS || nr < 0 || nr >= ROWS) continue;
      if (grid[nr][nc] === CELL.WALL) continue;

      const nk = key(nc, nr);
      if (inClosed[nk]) continue;

      const ng = gScore[cur.k] + 1;
      if (ng < gScore[nk]) {
        gScore[nk]   = ng;
        cameFrom[nk] = cur.k;
        const nf = ng + h(nc, nr);
        if (!inOpen[nk]) {
          open.push({ k: nk, c: nc, r: nr, f: nf });
          inOpen[nk] = 1;
        } else {
          for (const n of open) { if (n.k === nk) { n.f = nf; break; } }
        }
      }
    }
  }

  return { visitedSeq: visited, pathSeq: null };
}

// ════════════════════════════════════════════════════
//  Easing
// ════════════════════════════════════════════════════

function easeOutCubic(t) { return 1 - Math.pow(1 - t, 3); }

// ════════════════════════════════════════════════════
//  Animation Loop
// ════════════════════════════════════════════════════

function stopAnimation() {
  if (animFrameId !== null) { cancelAnimationFrame(animFrameId); animFrameId = null; }
  animState   = ANIM.IDLE;
  visitedSeq  = [];
  pathSeq     = null;
  visitIdx    = 0;
  pathIdx     = 0;
  activeFades = [];
}

/** Instant 모드: RAF 없이 즉시 결과 렌더 */
function applyInstant(vSeq, pSeq) {
  for (const { col, row } of vSeq)
    if (grid[row][col] === CELL.EMPTY) grid[row][col] = CELL.VISITED;

  if (!pSeq) {
    render(cellSize);
    animState = ANIM.DONE;
    showToast('⚠ 경로를 찾을 수 없습니다', 2800, false);
    setStatus('경로 없음 — 다른 위치를 클릭해보세요');
    return;
  }

  for (const { col, row } of pSeq) {
    const t = grid[row][col];
    if (t !== CELL.START && t !== CELL.END) grid[row][col] = CELL.PATH;
  }

  render(cellSize);
  animState = ANIM.DONE;
  setStatus(`경로 탐색 완료 — 최단 거리: ${pSeq.length - 1}칸`);
  showToast(`✓ 최단 경로: ${pSeq.length - 1}칸`, 2800, true);
}

function animLoop(now) {
  const spd = getSpeed();

  /* ── Phase 1: 방문 셀 순차 공개 ───────────────────── */
  if (animState === ANIM.VISITING) {
    const end = Math.min(visitIdx + spd.visitPerFrame, visitedSeq.length);
    while (visitIdx < end) {
      const { col, row } = visitedSeq[visitIdx++];
      if (grid[row][col] === CELL.EMPTY) {
        grid[row][col] = CELL.VISITED;
        if (spd.visitFade > 0)
          activeFades.push({ col, row, startTime: now, type: 'visited' });
      }
    }

    if (visitIdx >= visitedSeq.length) {
      const allFadeDone = spd.visitFade === 0 || activeFades.every(
        f => f.type !== 'visited' || (now - f.startTime) >= spd.visitFade
      );
      if (allFadeDone) {
        if (!pathSeq) {
          renderFrame(now);
          animState = ANIM.DONE;
          showToast('⚠ 경로를 찾을 수 없습니다', 2800, false);
          setStatus('경로 없음 — 다른 위치를 클릭해보세요');
          return;
        }
        activeFades = activeFades.filter(f => f.type !== 'visited');
        animState   = ANIM.PATHING;
        setStatus('경로 추적 중...');
      }
    }
  }

  /* ── Phase 2: 최적 경로 순차 공개 ─────────────────── */
  if (animState === ANIM.PATHING) {
    const end = Math.min(pathIdx + spd.pathPerFrame, pathSeq.length);
    while (pathIdx < end) {
      const { col, row } = pathSeq[pathIdx++];
      const t = grid[row][col];
      if (t !== CELL.START && t !== CELL.END) {
        grid[row][col] = CELL.PATH;
        if (spd.pathFade > 0)
          activeFades.push({ col, row, startTime: now, type: 'path' });
      }
    }

    if (pathIdx >= pathSeq.length) {
      const allFadeDone = spd.pathFade === 0 || activeFades.every(
        f => f.type !== 'path' || (now - f.startTime) >= spd.pathFade
      );
      if (allFadeDone) {
        renderFrame(now);
        animState = ANIM.DONE;
        setStatus(`경로 탐색 완료 — 최단 거리: ${pathSeq.length - 1}칸`);
        showToast(`✓ 최단 경로: ${pathSeq.length - 1}칸`, 2800, true);
        return;
      }
    }
  }

  renderFrame(now);

  if (animState === ANIM.VISITING || animState === ANIM.PATHING)
    animFrameId = requestAnimationFrame(animLoop);
}

// ════════════════════════════════════════════════════
//  Rendering
// ════════════════════════════════════════════════════

function renderFrame(now) {
  const spd = getSpeed();
  render(cellSize);

  activeFades = activeFades.filter(f => {
    const dur = f.type === 'path' ? spd.pathFade : spd.visitFade;
    return dur > 0 && (now - f.startTime) < dur;
  });

  for (const fade of activeFades) {
    const elapsed = now - fade.startTime;
    const dur     = fade.type === 'path' ? spd.pathFade : spd.visitFade;
    const t       = Math.min(elapsed / dur, 1);
    const x = CELL_GAP + fade.col * (cellSize + CELL_GAP);
    const y = CELL_GAP + fade.row * (cellSize + CELL_GAP);
    if (fade.type === 'visited') drawVisitedFade(x, y, cellSize, t);
    else                         drawPathFade(x, y, cellSize, t);
  }
}

function drawVisitedFade(x, y, size, t) {
  const ease  = easeOutCubic(t);
  const alpha = Math.max(0, 1 - ease);
  ctx.save();
  ctx.globalAlpha = alpha * 0.72;
  ctx.fillStyle   = '#818cf8';
  ctx.fillRect(x, y, size, size);
  const grad = ctx.createRadialGradient(
    x + size / 2, y + size / 2, 0,
    x + size / 2, y + size / 2, size * 0.7
  );
  grad.addColorStop(0, `rgba(129,140,248,${alpha * 0.6})`);
  grad.addColorStop(1, 'rgba(129,140,248,0)');
  ctx.fillStyle = grad;
  ctx.fillRect(x, y, size, size);
  ctx.restore();
}

function drawPathFade(x, y, size, t) {
  const ease  = easeOutCubic(t);
  const alpha = Math.max(0, 1 - ease);
  ctx.save();
  const scale = 1 + (1 - ease) * 0.35;
  const cx = x + size / 2, cy = y + size / 2;
  ctx.translate(cx, cy);
  ctx.scale(scale, scale);
  ctx.translate(-cx, -cy);
  ctx.globalAlpha = alpha * 0.85;
  ctx.fillStyle   = '#ffffff';
  ctx.fillRect(x, y, size, size);
  const grad = ctx.createRadialGradient(cx, cy, 0, cx, cy, size * 0.9);
  grad.addColorStop(0,   `rgba(132,204,22,${alpha * 0.5})`);
  grad.addColorStop(0.6, `rgba(132,204,22,${alpha * 0.25})`);
  grad.addColorStop(1,   'rgba(132,204,22,0)');
  ctx.fillStyle   = grad;
  ctx.globalAlpha = alpha;
  ctx.fillRect(x - size * 0.2, y - size * 0.2, size * 1.4, size * 1.4);
  ctx.restore();
}

function render(cs) {
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.fillStyle = COLOR.gridLine;
  ctx.fillRect(0, 0, canvas.width, canvas.height);
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      drawCell(
        CELL_GAP + c * (cs + CELL_GAP),
        CELL_GAP + r * (cs + CELL_GAP),
        cs, r, c, grid[r][c]
      );
}

function drawCell(x, y, size, row, col, type) {
  ctx.shadowBlur = 0;

  switch (type) {

    /* ── 출발점: 시안 글로우 + 십자 마크 ───────────── */
    case CELL.START: {
      ctx.shadowColor = COLOR.start;
      ctx.shadowBlur  = 12;
      ctx.fillStyle   = COLOR.start;
      ctx.fillRect(x, y, size, size);
      ctx.shadowBlur  = 0;
      ctx.fillStyle   = 'rgba(255,255,255,0.85)';
      const cx = x + size / 2, cy = y + size / 2;
      const arm = Math.max(1, size * 0.14), len = size * 0.42;
      ctx.fillRect(cx - arm, cy - len, arm * 2, len * 2);
      ctx.fillRect(cx - len, cy - arm, len * 2, arm * 2);
      break;
    }

    /* ── 도착점: 앰버 글로우 + X 마크 ─────────────── */
    case CELL.END: {
      ctx.shadowColor = COLOR.end;
      ctx.shadowBlur  = 14;
      ctx.fillStyle   = COLOR.end;
      ctx.fillRect(x, y, size, size);
      ctx.shadowBlur  = 0;
      ctx.fillStyle   = 'rgba(255,255,255,0.9)';
      const m = Math.max(2, size * 0.2), s = size;
      ctx.save();
      ctx.translate(x + s / 2, y + s / 2);
      ctx.rotate(Math.PI / 4);
      ctx.fillRect(-m / 2, -(s * 0.38), m, s * 0.76);
      ctx.rotate(Math.PI / 2);
      ctx.fillRect(-m / 2, -(s * 0.38), m, s * 0.76);
      ctx.restore();
      break;
    }

    /* ── 최적 경로: 라임 + 중앙 원형 점 ────────────── */
    case CELL.PATH: {
      ctx.shadowColor = COLOR.path;
      ctx.shadowBlur  = 6;
      ctx.fillStyle   = COLOR.path;
      ctx.fillRect(x, y, size, size);
      ctx.shadowBlur  = 0;
      ctx.fillStyle   = 'rgba(255,255,255,0.55)';
      ctx.beginPath();
      ctx.arc(x + size / 2, y + size / 2, Math.max(1, size * 0.18), 0, Math.PI * 2);
      ctx.fill();
      break;
    }

    /* ── 탐색 영역: 인디고 블루 ─────────────────────── */
    case CELL.VISITED: {
      ctx.fillStyle = COLOR.visited;
      ctx.fillRect(x, y, size, size);
      ctx.fillStyle = 'rgba(99,102,241,0.18)';
      ctx.fillRect(x, y, size, 1);
      ctx.fillRect(x, y, 1, size);
      break;
    }

    /* ── 장애물: 입체 엣지 ──────────────────────────── */
    case CELL.WALL: {
      ctx.fillStyle = COLOR.wall;
      ctx.fillRect(x, y, size, size);
      const e = Math.max(1, Math.floor(size * 0.22));
      ctx.fillStyle = COLOR.wallFace;
      ctx.fillRect(x,            y,            size, e);
      ctx.fillRect(x,            y,            e,    size);
      ctx.fillStyle = 'rgba(0,0,0,0.35)';
      ctx.fillRect(x + size - e, y,            e,    size);
      ctx.fillRect(x,            y + size - e, size, e);
      break;
    }

    /* ── 빈 셀: 체커보드 질감 ──────────────────────── */
    default: {
      ctx.fillStyle = (row + col) % 2 === 0 ? COLOR.empty : COLOR.emptyAlt;
      ctx.fillRect(x, y, size, size);
    }
  }
}

// ════════════════════════════════════════════════════
//  UI Helpers
// ════════════════════════════════════════════════════

function updateStats(walls) { wallCountEl.textContent = walls; }
function setStatus(msg)     { footerStatus.textContent = msg; }

function showToast(msg, ms = 2800, success = false) {
  clearTimeout(toastTimer);
  toast.textContent = msg;
  toast.classList.toggle('success', success);
  toast.classList.add('show');
  toastTimer = setTimeout(() => { toast.classList.remove('show'); }, ms);
}

// ════════════════════════════════════════════════════
//  Coordinate Helper
// ════════════════════════════════════════════════════

function pixelToCell(clientX, clientY) {
  const rect   = canvas.getBoundingClientRect();
  const scaleX = canvas.width  / rect.width;
  const scaleY = canvas.height / rect.height;
  const px = (clientX - rect.left) * scaleX;
  const py = (clientY - rect.top)  * scaleY;
  return {
    col: Math.floor(px / (cellSize + CELL_GAP)),
    row: Math.floor(py / (cellSize + CELL_GAP)),
  };
}

function isValidCell(col, row) {
  return col >= 0 && col < COLS && row >= 0 && row < ROWS;
}

// ════════════════════════════════════════════════════
//  Search Trigger  (목적지 지정 + A* 실행)
// ════════════════════════════════════════════════════

function triggerSearch(col, row) {
  if (!isValidCell(col, row)) return;
  if (grid[row][col] === CELL.WALL)                    return;
  if (row === startRow && col === startCol)             return;

  stopAnimation();
  clearPathState();
  grid[row][col] = CELL.END;
  render(cellSize);
  setStatus('A* 탐색 중...');

  const result = runAStar(startCol, startRow, col, row);
  visitedSeq   = result.visitedSeq;
  pathSeq      = result.pathSeq;
  visitIdx     = 0;
  pathIdx      = 0;

  if (speedKey === 'instant') {
    applyInstant(visitedSeq, pathSeq);
  } else {
    animState   = ANIM.VISITING;
    animFrameId = requestAnimationFrame(animLoop);
  }
}

// ════════════════════════════════════════════════════
//  Mouse Events — L-Click / Drag
//  · mousedown  : 드래그 준비, dragMode 결정
//  · mousemove  : 첫 셀 이탈 시 드래그 확정 → 벽 토글
//  · mouseup    : hasDragged=false → 클릭(목적지) / true → 벽 편집 완료
// ════════════════════════════════════════════════════

canvas.addEventListener('mousedown', (e) => {
  if (e.button !== 0) return;

  const { col, row } = pixelToCell(e.clientX, e.clientY);
  if (!isValidCell(col, row)) return;

  isDragging   = true;
  hasDragged   = false;
  lastDragCell = { col, row };

  // 시작 셀 타입에 따라 드래그 모드 결정
  dragMode = grid[row][col] === CELL.WALL ? 'remove' : 'add';

  e.preventDefault(); // 텍스트 선택 방지
});

canvas.addEventListener('mousemove', (e) => {
  if (!isDragging) return;

  const { col, row } = pixelToCell(e.clientX, e.clientY);
  if (!isValidCell(col, row)) return;
  if (lastDragCell && lastDragCell.col === col && lastDragCell.row === row) return;

  // 새 셀 진입 → 드래그 확정
  if (!hasDragged) {
    hasDragged = true;
    // 첫 드래그 시 애니메이션·경로 클리어
    stopAnimation();
    clearPathState();
    setStatus('벽 편집 중 — 마우스를 놓으면 완료');
  }

  lastDragCell = { col, row };

  // START · END 셀은 보호
  const cellType = grid[row][col];
  if (cellType === CELL.START || cellType === CELL.END) return;

  if (dragMode === 'add' && cellType !== CELL.WALL) {
    grid[row][col] = CELL.WALL;
    render(cellSize);
  } else if (dragMode === 'remove' && cellType === CELL.WALL) {
    grid[row][col] = CELL.EMPTY;
    render(cellSize);
  }
});

// canvas 안에서 mouseup
canvas.addEventListener('mouseup', (e) => {
  if (e.button !== 0 || !isDragging) return;
  isDragging = false;

  if (!hasDragged) {
    // 일반 클릭 → 목적지 지정
    const { col, row } = pixelToCell(e.clientX, e.clientY);
    triggerSearch(col, row);
  } else {
    // 드래그 완료 → 벽 통계 갱신
    updateStats(countWalls());
    setStatus('벽 편집 완료 — 클릭: 경로 탐색 | 우클릭: 시작점 이동');
  }

  lastDragCell = null;
});

// canvas 밖에서도 mouseup 처리 (캔버스 이탈 후 버튼 놓은 경우)
window.addEventListener('mouseup', (e) => {
  if (e.button !== 0 || !isDragging) return;
  isDragging = false;
  if (hasDragged) {
    updateStats(countWalls());
    setStatus('벽 편집 완료 — 클릭: 경로 탐색 | 우클릭: 시작점 이동');
    render(cellSize);
  }
  lastDragCell = null;
});

// 드래그 중 이미지 드래그 방지
canvas.addEventListener('dragstart', (e) => e.preventDefault());

// ════════════════════════════════════════════════════
//  Right-Click — 시작점 이동
// ════════════════════════════════════════════════════

canvas.addEventListener('contextmenu', (e) => {
  e.preventDefault(); // 브라우저 기본 메뉴 차단

  const { col, row } = pixelToCell(e.clientX, e.clientY);
  if (!isValidCell(col, row))              return;
  if (grid[row][col] === CELL.WALL)        return; // 벽 위 이동 불가
  if (row === startRow && col === startCol) return; // 현재 시작점 재클릭 무시

  stopAnimation();
  clearPathState();

  // 기존 START 셀 비우기
  grid[startRow][startCol] = CELL.EMPTY;

  // 새 시작점 설정 (세션 유지 — F5 전까지 보존)
  startCol = col;
  startRow = row;
  grid[startRow][startCol] = CELL.START;

  render(cellSize);
  setStatus(`시작점 이동 → (${col}, ${row}) — 클릭: 경로 탐색`);
  showToast(`✦ 시작점 이동: (${col}, ${row})`, 1800, false);
});

// ════════════════════════════════════════════════════
//  Speed Controller
// ════════════════════════════════════════════════════

speedSelect.addEventListener('change', () => {
  speedKey = speedSelect.value;
  // 속도는 다음 탐색부터 즉시 적용 (진행 중 애니메이션에도 반영)
});

// ════════════════════════════════════════════════════
//  Refresh Map
// ════════════════════════════════════════════════════

function refreshMap() {
  stopAnimation();

  btnRefresh.classList.add('refreshing');
  btnRefresh.addEventListener('animationend', () => {
    btnRefresh.classList.remove('refreshing');
  }, { once: true });

  const cell  = resizeCanvas();
  const walls = initGrid(); // startCol/startRow 는 유지됨
  render(cell);
  updateStats(walls);
  setStatus('랜덤 맵 생성 완료 — 클릭: 도착점 | 우클릭: 시작점 이동 | 드래그: 벽 편집');
}

btnRefresh.addEventListener('click', refreshMap);

document.addEventListener('keydown', (e) => {
  if ((e.key === 'r' || e.key === 'R') && !e.ctrlKey && !e.metaKey)
    refreshMap();
});

let resizeTimer = null;
window.addEventListener('resize', () => {
  clearTimeout(resizeTimer);
  resizeTimer = setTimeout(() => { render(resizeCanvas()); }, 120);
});

// ════════════════════════════════════════════════════
//  Bootstrap
// ════════════════════════════════════════════════════
(function init() {
  const cell  = resizeCanvas();
  const walls = initGrid();
  render(cell);
  updateStats(walls);
  setStatus('맵 초기화 완료 — 클릭: 도착점 | 우클릭: 시작점 이동 | 드래그: 벽 편집');
})();
