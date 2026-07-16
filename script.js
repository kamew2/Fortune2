/* ════════════════════════════════════════════════════
   2D Grid Map — A* Pathfinding Visualizer
   Grid : COLS(40) × ROWS(20)
   Start: (col=2, row=2) — 0-indexed, fixed
   Walls: ~25%  (Fisher-Yates shuffle)

   Animation pipeline
   ──────────────────
   Click → A*(sync) → [VISITING phase] → [PATHING phase] → DONE
   ════════════════════════════════════════════════════ */

'use strict';

// ════════════════════════════════════════════════════
//  Config
// ════════════════════════════════════════════════════
const COLS       = 40;
const ROWS       = 20;
const WALL_RATIO = 0.25;
const START_COL  = 2;
const START_ROW  = 2;
const CELL_GAP   = 1;   // 1px 그리드 선

/**
 * 방문 셀 공개 속도 (셀/프레임).
 * 60fps 기준: 약 800ms 내 전체 탐색 영역 표시.
 */
const VISIT_PER_FRAME = 6;

/**
 * 경로 셀 공개 속도 (셀/프레임).
 * 1로 설정 시 셀 하나씩 순차 등장.
 */
const PATH_PER_FRAME = 1;

/**
 * 방문 셀 페이드-인 애니메이션 지속 시간 (ms).
 * 각 셀이 등장할 때 알파가 0→1로 부드럽게 변화.
 */
const VISIT_FADE_DURATION = 280;

/**
 * 경로 셀 강조 애니메이션 지속 시간 (ms).
 */
const PATH_FADE_DURATION  = 180;

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

// A* 결과 시퀀스
let visitedSeq  = [];   // [{col, row}] — A*가 방문한 순서
let pathSeq     = null; // [{col, row}] | null — 최적 경로(출발→도착)

// 커서
let visitIdx    = 0;
let pathIdx     = 0;

// 페이드-인 애니메이션을 위한 활성 셀 목록
// { col, row, startTime, type: 'visited'|'path' }
let activeFades = [];

// ════════════════════════════════════════════════════
//  Grid State
// ════════════════════════════════════════════════════
let grid       = [];   // grid[row][col] = CELL.*
let cellSize   = 20;   // px — resizeCanvas() 갱신
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

// ════════════════════════════════════════════════════
//  Colour Map  (CSS → JS 단일 진실 원천)
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

/** 컨테이너에 맞춰 canvas 크기 조정 */
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

/** Fisher-Yates 셔플로 25% 랜덤 장애물 배치 */
function initGrid() {
  const wallTarget = Math.round(ROWS * COLS * WALL_RATIO);
  grid = Array.from({ length: ROWS }, () => new Uint8Array(COLS));
  grid[START_ROW][START_COL] = CELL.START;

  const idx = [];
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      if (!(r === START_ROW && c === START_COL)) idx.push(r * COLS + c);

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

// ════════════════════════════════════════════════════
//  A* Algorithm
// ════════════════════════════════════════════════════

/**
 * A* — Manhattan 휴리스틱, 4방향
 * @returns {{ visitedSeq: {col,row}[], pathSeq: {col,row}[]|null }}
 */
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
//  Easing Helpers
// ════════════════════════════════════════════════════

/** ease-out cubic: 빠르게 시작 → 부드럽게 마무리 */
function easeOutCubic(t) { return 1 - Math.pow(1 - t, 3); }

/** ease-in-out sine */
function easeInOutSine(t) { return -(Math.cos(Math.PI * t) - 1) / 2; }

// ════════════════════════════════════════════════════
//  Animation Loop
// ════════════════════════════════════════════════════

/**
 * 진행 중인 RAF를 취소하고 애니메이션 상태를 초기화한다.
 */
function stopAnimation() {
  if (animFrameId !== null) {
    cancelAnimationFrame(animFrameId);
    animFrameId = null;
  }
  animState   = ANIM.IDLE;
  visitedSeq  = [];
  pathSeq     = null;
  visitIdx    = 0;
  pathIdx     = 0;
  activeFades = [];
}

/**
 * 메인 애니메이션 루프.
 * VISITING → (path 있음) PATHING → DONE
 *           → (path 없음) DONE + toast
 *
 * @param {DOMHighResTimeStamp} now  — rAF 타임스탬프
 */
function animLoop(now) {
  /* ── Phase 1: 방문 셀 순차 공개 ───────────────────── */
  if (animState === ANIM.VISITING) {
    const end = Math.min(visitIdx + VISIT_PER_FRAME, visitedSeq.length);
    while (visitIdx < end) {
      const { col, row } = visitedSeq[visitIdx++];
      // START · END · WALL 은 보존
      if (grid[row][col] === CELL.EMPTY) {
        grid[row][col] = CELL.VISITED;
        activeFades.push({ col, row, startTime: now, type: 'visited' });
      }
    }

    if (visitIdx >= visitedSeq.length) {
      // 방문 완료 → 페이드 끝날 때까지 잠깐 대기 후 전환
      const allFadeDone = activeFades.every(
        f => f.type !== 'visited' || (now - f.startTime) >= VISIT_FADE_DURATION
      );
      if (allFadeDone) {
        if (!pathSeq) {
          renderFrame(now);
          animState = ANIM.DONE;
          showToast('⚠ 경로를 찾을 수 없습니다', 2800, false);
          setStatus('경로 없음 — 다른 위치를 클릭해보세요');
          return;
        }
        // visited 페이드 완료 → 경로 단계로 전환
        activeFades = activeFades.filter(f => f.type !== 'visited');
        animState   = ANIM.PATHING;
        setStatus('경로 추적 중...');
      }
    }
  }

  /* ── Phase 2: 최적 경로 순차 공개 ─────────────────── */
  if (animState === ANIM.PATHING) {
    const end = Math.min(pathIdx + PATH_PER_FRAME, pathSeq.length);
    while (pathIdx < end) {
      const { col, row } = pathSeq[pathIdx++];
      const t = grid[row][col];
      if (t !== CELL.START && t !== CELL.END) {
        grid[row][col] = CELL.PATH;
        activeFades.push({ col, row, startTime: now, type: 'path' });
      }
    }

    if (pathIdx >= pathSeq.length) {
      // 마지막 path 페이드까지 기다리기
      const allFadeDone = activeFades.every(
        f => f.type !== 'path' || (now - f.startTime) >= PATH_FADE_DURATION
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

/**
 * 매 프레임 전체 그리드를 렌더링 + 활성 페이드 셀 오버레이
 * @param {DOMHighResTimeStamp} now
 */
function renderFrame(now) {
  render(cellSize);

  // 만료된 페이드 제거
  activeFades = activeFades.filter(f => {
    const dur = f.type === 'path' ? PATH_FADE_DURATION : VISIT_FADE_DURATION;
    return (now - f.startTime) < dur;
  });

  // 활성 페이드 오버레이 렌더링
  for (const fade of activeFades) {
    const elapsed = now - fade.startTime;
    const dur     = fade.type === 'path' ? PATH_FADE_DURATION : VISIT_FADE_DURATION;
    const t       = Math.min(elapsed / dur, 1);

    const x = CELL_GAP + fade.col * (cellSize + CELL_GAP);
    const y = CELL_GAP + fade.row * (cellSize + CELL_GAP);

    if (fade.type === 'visited') {
      drawVisitedFade(x, y, cellSize, t);
    } else {
      drawPathFade(x, y, cellSize, t);
    }
  }
}

/**
 * 방문 셀 페이드-인: 밝은 인디고 → 어두운 인디고로 수렴
 * 초기에 밝은 펄스를 내고 fade out으로 고정 색에 착지.
 */
function drawVisitedFade(x, y, size, t) {
  // t=0: 밝은 시안 플래시, t=1: 완전 visited 색으로 착지
  const ease  = easeOutCubic(t);
  // 오버레이: 처음에 밝은 청보라 빛 → 투명으로
  const alpha = Math.max(0, 1 - ease);
  ctx.save();
  ctx.globalAlpha = alpha * 0.72;
  ctx.fillStyle   = '#818cf8'; // 밝은 인디고
  ctx.fillRect(x, y, size, size);

  // 중심 원형 글로우
  const grad = ctx.createRadialGradient(
    x + size / 2, y + size / 2, 0,
    x + size / 2, y + size / 2, size * 0.7
  );
  grad.addColorStop(0,   `rgba(129,140,248,${alpha * 0.6})`);
  grad.addColorStop(1,   'rgba(129,140,248,0)');
  ctx.fillStyle = grad;
  ctx.fillRect(x, y, size, size);
  ctx.restore();
}

/**
 * 경로 셀 페이드-인: 초기 밝은 화이트 플래시 → 라임 그린으로 착지
 */
function drawPathFade(x, y, size, t) {
  const ease  = easeOutCubic(t);
  const alpha = Math.max(0, 1 - ease);

  ctx.save();
  // 스케일 펄스 (중심에서 약간 확대되며 등장)
  const scale  = 1 + (1 - ease) * 0.35;
  const cx     = x + size / 2;
  const cy     = y + size / 2;
  ctx.translate(cx, cy);
  ctx.scale(scale, scale);
  ctx.translate(-cx, -cy);

  // 밝은 화이트 플래시 오버레이
  ctx.globalAlpha = alpha * 0.85;
  ctx.fillStyle   = '#ffffff';
  ctx.fillRect(x, y, size, size);

  // 라임 글로우 링
  const grad = ctx.createRadialGradient(cx, cy, 0, cx, cy, size * 0.9);
  grad.addColorStop(0,   `rgba(132,204,22,${alpha * 0.5})`);
  grad.addColorStop(0.6, `rgba(132,204,22,${alpha * 0.25})`);
  grad.addColorStop(1,   'rgba(132,204,22,0)');
  ctx.fillStyle   = grad;
  ctx.globalAlpha = alpha;
  ctx.fillRect(x - size * 0.2, y - size * 0.2, size * 1.4, size * 1.4);

  ctx.restore();
}

/**
 * 전체 그리드를 canvas에 렌더링 (정적 스냅샷)
 */
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

    /* ── 탐색 영역: 인디고 블루 ──────────────────────── */
    case CELL.VISITED: {
      ctx.fillStyle = COLOR.visited;
      ctx.fillRect(x, y, size, size);
      // 미세 내부 글로우 (테두리 밝게)
      ctx.fillStyle = 'rgba(99,102,241,0.18)';
      ctx.fillRect(x, y, size, 1);
      ctx.fillRect(x, y, 1, size);
      break;
    }

    /* ── 장애물: 입체 엣지 ───────────────────────────── */
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
  toastTimer = setTimeout(() => {
    toast.classList.remove('show');
  }, ms);
}

// ════════════════════════════════════════════════════
//  Click Handler  (도착점 지정 + A* 시작)
// ════════════════════════════════════════════════════

/** CSS 스케일 보정 포함 픽셀 → 그리드 좌표 변환 */
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

canvas.addEventListener('click', (e) => {
  const { col, row } = pixelToCell(e.clientX, e.clientY);

  // 유효성 검사
  if (col < 0 || col >= COLS || row < 0 || row >= ROWS) return;
  if (grid[row][col] === CELL.WALL)  return;
  if (row === START_ROW && col === START_COL) return;

  // ① 이전 애니메이션 완전 종료 + 상태 초기화
  stopAnimation();
  // ② 이전 탐색 결과 그리드에서 지우기
  clearPathState();
  // ③ 도착점 설정 후 즉시 렌더
  grid[row][col] = CELL.END;
  render(cellSize);
  setStatus('A* 탐색 중...');

  // ④ A* 동기 실행 (800셀 — 체감 지연 없음)
  const result = runAStar(START_COL, START_ROW, col, row);
  visitedSeq   = result.visitedSeq;
  pathSeq      = result.pathSeq;
  visitIdx     = 0;
  pathIdx      = 0;

  // ⑤ 애니메이션 시작
  animState   = ANIM.VISITING;
  animFrameId = requestAnimationFrame(animLoop);
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
  const walls = initGrid();
  render(cell);
  updateStats(walls);
  setStatus('랜덤 맵 생성 완료 — 그리드를 클릭하여 도착점을 지정하세요');
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
  setStatus('맵 초기화 완료 — 그리드를 클릭하여 도착점을 지정하세요');
})();
