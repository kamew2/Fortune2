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
   Speed Select → 0.1x / 0.3x / 0.5x / 1x / 2x / 5x / Instant
   Visited      → Rainbow HSL (탐색 순서 기반 무지개 색상)
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
//  msPerStep > 0  → 슬로우 모드: N ms 경과 시 1스텝
//  msPerStep = 0  → 일반 모드: 매 프레임 visitPerStep 셀 처리
// ════════════════════════════════════════════════════
const SPEED_PRESETS = {
  '0.1':     { visitPerStep:  1, pathPerStep: 1, visitFade: 500, pathFade: 300, msPerStep: 200 },
  '0.3':     { visitPerStep:  1, pathPerStep: 1, visitFade: 300, pathFade: 200, msPerStep:  66 },
  '0.5':     { visitPerStep:  1, pathPerStep: 1, visitFade: 200, pathFade: 140, msPerStep:  33 },
  '1':       { visitPerStep:  4, pathPerStep: 1, visitFade: 280, pathFade: 180, msPerStep:   0 },
  '2':       { visitPerStep: 10, pathPerStep: 2, visitFade: 150, pathFade:  90, msPerStep:   0 },
  '5':       { visitPerStep: 30, pathPerStep: 4, visitFade:  70, pathFade:  40, msPerStep:   0 },
  'instant': { visitPerStep: Infinity, pathPerStep: Infinity, visitFade: 0, pathFade: 0, msPerStep: 0 },
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

let animState    = ANIM.IDLE;
let animFrameId  = null;
let visitedSeq   = [];
let pathSeq      = null;
let visitIdx     = 0;
let pathIdx      = 0;
let activeFades  = [];
let lastStepTime = 0; // 슬로우 모드용 타임스탬프

// ── Rainbow 색상 시스템 ──────────────────────────────
// visitOrderGrid : 각 셀이 몇 번째로 방문됐는지 기록 (Uint16, max 800)
// visitedTotal   : visitedSeq.length — hue 정규화 기준
let visitOrderGrid = null;
let visitedTotal   = 0;

// ════════════════════════════════════════════════════
//  Drag State  (L-Click 드래그 → 벽 토글)
// ════════════════════════════════════════════════════
let isDragging   = false;
let hasDragged   = false;
let dragMode     = null;   // 'add' | 'remove'
let lastDragCell = null;   // { col, row }

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
  gridLine: cv.getPropertyValue('--cell-grid-line').trim()|| 'rgba(99,102,241,0.09)',
};

// ════════════════════════════════════════════════════
//  Rainbow Hue System
// ════════════════════════════════════════════════════

/**
 * 방문 순서 인덱스 → HSL Hue (0→300)
 * 0   = 빨강(Red)
 * 60  = 노랑(Yellow)
 * 120 = 초록(Green)
 * 180 = 청록(Cyan)
 * 240 = 파랑(Blue)
 * 300 = 보라(Violet)
 */
function visitHue(orderIdx) {
  if (!visitedTotal) return 240;
  return (orderIdx / visitedTotal) * 300;
}

/** hue → 셀 베이스 색상 문자열 */
function visitColor(hue) {
  return `hsl(${hue.toFixed(1)}, 72%, 32%)`;
}

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

/** Fisher-Yates 셔플로 25% 랜덤 장애물 배치 (startCol/startRow 유지) */
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

/** VISITED · PATH · END 셀 → EMPTY */
function clearPathState() {
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++) {
      const t = grid[r][c];
      if (t === CELL.VISITED || t === CELL.PATH || t === CELL.END)
        grid[r][c] = CELL.EMPTY;
    }
}

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
  animState      = ANIM.IDLE;
  visitedSeq     = [];
  pathSeq        = null;
  visitIdx       = 0;
  pathIdx        = 0;
  activeFades    = [];
  lastStepTime   = 0;
  visitOrderGrid = null;
  visitedTotal   = 0;
}

/** Instant 모드: RAF 없이 즉시 최종 상태 렌더 */
function applyInstant(vSeq, pSeq) {
  for (let i = 0; i < vSeq.length; i++) {
    const { col, row } = vSeq[i];
    if (grid[row][col] === CELL.EMPTY) {
      grid[row][col] = CELL.VISITED;
      if (visitOrderGrid) visitOrderGrid[row * COLS + col] = i;
    }
  }

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

/**
 * 메인 애니메이션 루프
 * 슬로우 모드(msPerStep > 0): 경과 시간이 msPerStep 이상일 때만 다음 스텝 진행
 * 일반/고속 모드(msPerStep = 0): 매 프레임 visitPerStep 만큼 처리
 */
function animLoop(now) {
  const spd = getSpeed();

  /* ── Phase 1: 방문 셀 순차 공개 ───────────────────── */
  if (animState === ANIM.VISITING) {
    // 슬로우 모드 타임게이트
    const canStep = spd.msPerStep === 0 || (now - lastStepTime) >= spd.msPerStep;

    if (canStep && visitIdx < visitedSeq.length) {
      if (spd.msPerStep > 0) lastStepTime = now;

      const end = Math.min(visitIdx + spd.visitPerStep, visitedSeq.length);
      while (visitIdx < end) {
        const { col, row } = visitedSeq[visitIdx];
        const orderIdx     = visitIdx; // 방문 순서 캡처 (무지개 색상용)
        visitIdx++;

        if (grid[row][col] === CELL.EMPTY) {
          grid[row][col] = CELL.VISITED;
          // 방문 순서 기록
          if (visitOrderGrid) visitOrderGrid[row * COLS + col] = orderIdx;

          if (spd.visitFade > 0) {
            const hue = visitHue(orderIdx);
            activeFades.push({ col, row, startTime: now, type: 'visited', hue });
          }
        }
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
        activeFades  = activeFades.filter(f => f.type !== 'visited');
        animState    = ANIM.PATHING;
        lastStepTime = 0; // 경로 단계 타이머 리셋
        setStatus('경로 추적 중...');
      }
    }
  }

  /* ── Phase 2: 최적 경로 순차 공개 ─────────────────── */
  if (animState === ANIM.PATHING) {
    const canStep = spd.msPerStep === 0 || (now - lastStepTime) >= spd.msPerStep;

    if (canStep && pathIdx < pathSeq.length) {
      if (spd.msPerStep > 0) lastStepTime = now;

      const end = Math.min(pathIdx + spd.pathPerStep, pathSeq.length);
      while (pathIdx < end) {
        const { col, row } = pathSeq[pathIdx++];
        const t = grid[row][col];
        if (t !== CELL.START && t !== CELL.END) {
          grid[row][col] = CELL.PATH;
          if (spd.pathFade > 0)
            activeFades.push({ col, row, startTime: now, type: 'path' });
        }
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

  // 만료된 페이드 제거
  activeFades = activeFades.filter(f => {
    const dur = f.type === 'path' ? spd.pathFade : spd.visitFade;
    return dur > 0 && (now - f.startTime) < dur;
  });

  // 활성 페이드 오버레이 렌더링
  for (const fade of activeFades) {
    const elapsed = now - fade.startTime;
    const dur     = fade.type === 'path' ? spd.pathFade : spd.visitFade;
    const t       = Math.min(elapsed / dur, 1);
    const x = CELL_GAP + fade.col * (cellSize + CELL_GAP);
    const y = CELL_GAP + fade.row * (cellSize + CELL_GAP);
    if (fade.type === 'visited') drawVisitedFade(x, y, cellSize, t, fade.hue ?? 240);
    else                         drawPathFade(x, y, cellSize, t);
  }
}

/**
 * 방문 셀 페이드-인: 해당 셀의 hue 색상으로 밝은 플래시 → 고정 색 착지
 * @param {number} hue - visitHue(orderIdx) 로 계산된 색상
 */
function drawVisitedFade(x, y, size, t, hue) {
  const ease  = easeOutCubic(t);
  const alpha = Math.max(0, 1 - ease);

  ctx.save();
  // 밝은 플래시 (해당 hue 고채도)
  ctx.globalAlpha = alpha * 0.78;
  ctx.fillStyle   = `hsl(${hue.toFixed(1)}, 90%, 66%)`;
  ctx.fillRect(x, y, size, size);

  // 방사형 글로우
  const grad = ctx.createRadialGradient(
    x + size / 2, y + size / 2, 0,
    x + size / 2, y + size / 2, size * 0.78
  );
  grad.addColorStop(0, `hsla(${hue.toFixed(1)}, 90%, 62%, ${alpha * 0.65})`);
  grad.addColorStop(1, `hsla(${hue.toFixed(1)}, 90%, 62%, 0)`);
  ctx.fillStyle = grad;
  ctx.fillRect(x, y, size, size);

  ctx.restore();
}

/**
 * 경로 셀 페이드-인: 화이트 플래시 → 라임 그린 착지 + 스케일 펄스
 */
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

/** 전체 그리드 정적 렌더링 */
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

    /* ── 탐색 영역: 무지개 HSL (방문 순서 → hue 0~300) */
    case CELL.VISITED: {
      const orderIdx = (visitOrderGrid && visitOrderGrid[row * COLS + col]) || 0;
      const hue      = visitHue(orderIdx);
      ctx.fillStyle  = visitColor(hue);
      ctx.fillRect(x, y, size, size);
      // 상단·좌측 하이라이트 (입체감)
      ctx.fillStyle = `hsla(${hue.toFixed(1)}, 80%, 62%, 0.18)`;
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
  if (!isValidCell(col, row))               return;
  if (grid[row][col] === CELL.WALL)         return;
  if (row === startRow && col === startCol) return;

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

  // 무지개 색상 시스템 초기화
  visitedTotal   = visitedSeq.length;
  visitOrderGrid = new Uint16Array(ROWS * COLS); // 0으로 초기화됨

  if (speedKey === 'instant') {
    applyInstant(visitedSeq, pathSeq);
  } else {
    animState   = ANIM.VISITING;
    animFrameId = requestAnimationFrame(animLoop);
  }
}

// ════════════════════════════════════════════════════
//  Mouse Events — L-Click / Drag
//  mousedown  → 드래그 준비, dragMode 결정
//  mousemove  → 첫 셀 이탈 시 드래그 확정 → 벽 토글
//  mouseup    → hasDragged=false: 클릭(목적지) / true: 벽 편집 완료
// ════════════════════════════════════════════════════

canvas.addEventListener('mousedown', (e) => {
  if (e.button !== 0) return;
  const { col, row } = pixelToCell(e.clientX, e.clientY);
  if (!isValidCell(col, row)) return;

  isDragging   = true;
  hasDragged   = false;
  lastDragCell = { col, row };
  dragMode     = grid[row][col] === CELL.WALL ? 'remove' : 'add';
  e.preventDefault();
});

canvas.addEventListener('mousemove', (e) => {
  if (!isDragging) return;
  const { col, row } = pixelToCell(e.clientX, e.clientY);
  if (!isValidCell(col, row)) return;
  if (lastDragCell && lastDragCell.col === col && lastDragCell.row === row) return;

  if (!hasDragged) {
    hasDragged = true;
    stopAnimation();
    clearPathState();
    setStatus('벽 편집 중 — 마우스를 놓으면 완료');
  }

  lastDragCell = { col, row };

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

canvas.addEventListener('mouseup', (e) => {
  if (e.button !== 0 || !isDragging) return;
  isDragging = false;

  if (!hasDragged) {
    const { col, row } = pixelToCell(e.clientX, e.clientY);
    triggerSearch(col, row);
  } else {
    updateStats(countWalls());
    setStatus('벽 편집 완료 — 클릭: 경로 탐색 | 우클릭: 시작점 이동');
  }
  lastDragCell = null;
});

// 캔버스 이탈 후 mouseup
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

canvas.addEventListener('dragstart', (e) => e.preventDefault());

// ════════════════════════════════════════════════════
//  Right-Click — 시작점 이동
// ════════════════════════════════════════════════════

canvas.addEventListener('contextmenu', (e) => {
  e.preventDefault();
  const { col, row } = pixelToCell(e.clientX, e.clientY);
  if (!isValidCell(col, row))               return;
  if (grid[row][col] === CELL.WALL)         return;
  if (row === startRow && col === startCol) return;

  stopAnimation();
  clearPathState();
  grid[startRow][startCol] = CELL.EMPTY;

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
  const walls = initGrid(); // startCol/startRow 유지
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
