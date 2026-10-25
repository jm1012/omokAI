/*
 * 화면 그리기와 입력 처리 (Omok.py 의 pygame 부분을 옮긴 파일)
 * 사람은 흑, AI 는 백. AI 계산은 Web Worker 에서 실행
 */
(function () {
  const { GameState } = window.OmokEngine;
  const DIMENSION = 15;
  const COLS = 'ABCDEFGHJKLMNOP'; // 바둑판 표기 관례대로 I 는 건너뜀
  const STAR_POINTS = [[3, 3], [3, 11], [11, 3], [11, 11], [7, 7]];

  const canvas = document.getElementById('board');
  const ctx = canvas.getContext('2d');
  const statusEl = document.getElementById('status');
  const turnEl = document.getElementById('turn-stone');
  const moveCountEl = document.getElementById('move-count');
  const lastMoveEl = document.getElementById('last-move');
  const aiTimeEl = document.getElementById('ai-time');
  const logEl = document.getElementById('log');
  const undoBtn = document.getElementById('undo');
  const newBtn = document.getElementById('new-game');
  const copyBtn = document.getElementById('copy-log');
  const forbidToggle = document.getElementById('show-forbidden');

  const IMAGES = {};
  for (const [k, src] of [['b', 'images/black_stone_simple.png'], ['w', 'images/white_stone_simple.png'], ['f', 'images/forbidden_mark.png']]) {
    const img = new Image();
    img.onload = draw;
    img.src = src;
    IMAGES[k] = img;
  }

  let gs = new GameState();
  let thinking = false;
  let hover = null;
  let winLine = null;
  let forbiddenCache = null;
  let requestId = 0;

  // ---------- AI 연결 (Worker 를 못 쓰는 환경이면 메인 스레드에서 계산) ----------
  let worker = null;
  try {
    worker = new Worker('ai-worker.js');
  } catch (e) {
    worker = null;
  }
  let fallbackLoading = null;
  function loadFallbackAI() {
    if (window.OmokAI) return Promise.resolve();
    if (!fallbackLoading) {
      fallbackLoading = new Promise((resolve, reject) => {
        const s = document.createElement('script');
        s.src = 'ai.js';
        s.onload = resolve;
        s.onerror = reject;
        document.head.appendChild(s);
      });
    }
    return fallbackLoading;
  }

  function askAI(state) {
    const id = ++requestId;
    return new Promise((resolve) => {
      const runHere = () => {
        loadFallbackAI().then(() => {
          setTimeout(() => {
            const t0 = performance.now();
            const res = window.OmokAI.aiMove(window.OmokAI.restore(state));
            resolve({ id, ...res, ms: performance.now() - t0 });
          }, 30);
        });
      };
      if (!worker) return runHere();
      const w = worker;
      const onMsg = (e) => {
        if (e.data.id !== id) return;
        w.removeEventListener('message', onMsg);
        resolve(e.data);
      };
      // Worker 를 불러오지 못하면 메인 스레드에서 다시 계산
      w.addEventListener('error', () => {
        if (worker === w) worker = null;
        runHere();
      }, { once: true });
      w.addEventListener('message', onMsg);
      w.postMessage({ id, state });
    });
  }

  // ---------- 좌표 / 그리기 ----------
  function geometry() {
    const size = canvas.clientWidth;
    const margin = size * 0.075;
    const step = (size - margin * 2) / (DIMENSION - 1);
    return { size, margin, step };
  }

  function resize() {
    const dpr = window.devicePixelRatio || 1;
    const size = canvas.clientWidth;
    canvas.width = Math.round(size * dpr);
    canvas.height = Math.round(size * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    draw();
  }

  function css(name) {
    return getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  }

  function label(x, y) {
    return COLS[x] + (DIMENSION - y);
  }

  function forbiddenPoints() {
    if (forbiddenCache) return forbiddenCache;
    const pts = [];
    if (gs.blackToPlay && !gs.blackWin && !gs.whiteWin) {
      for (let x = 0; x < DIMENSION; x++)
        for (let y = 0; y < DIMENSION; y++)
          if (gs.board[x][y] === '-' && !gs.isWin([x, y]) && gs.getForbiddenMove([x, y])) pts.push([x, y]);
    }
    forbiddenCache = pts;
    return pts;
  }

  function draw() {
    const { size, margin, step } = geometry();
    if (!size) return;
    ctx.clearRect(0, 0, size, size);

    // 바둑판 나무 면
    ctx.fillStyle = css('--wood');
    ctx.fillRect(0, 0, size, size);
    const grain = ctx.createLinearGradient(0, 0, size, size);
    grain.addColorStop(0, 'rgba(255,255,255,0.10)');
    grain.addColorStop(1, 'rgba(0,0,0,0.08)');
    ctx.fillStyle = grain;
    ctx.fillRect(0, 0, size, size);

    // 선
    const ink = css('--board-ink');
    ctx.strokeStyle = ink;
    ctx.lineWidth = Math.max(1, size / 700);
    ctx.beginPath();
    for (let i = 0; i < DIMENSION; i++) {
      const p = margin + i * step;
      ctx.moveTo(margin, p); ctx.lineTo(size - margin, p);
      ctx.moveTo(p, margin); ctx.lineTo(p, size - margin);
    }
    ctx.stroke();
    ctx.lineWidth = Math.max(1.5, size / 350);
    ctx.strokeRect(margin, margin, step * (DIMENSION - 1), step * (DIMENSION - 1));

    // 화점
    ctx.fillStyle = ink;
    for (const [x, y] of STAR_POINTS) {
      ctx.beginPath();
      ctx.arc(margin + x * step, margin + y * step, step * 0.11, 0, Math.PI * 2);
      ctx.fill();
    }

    // 좌표 표기
    ctx.fillStyle = ink;
    ctx.font = `${Math.max(9, step * 0.32)}px ${css('--font-mono')}`;
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    for (let i = 0; i < DIMENSION; i++) {
      const p = margin + i * step;
      ctx.fillText(COLS[i], p, margin * 0.42);
      ctx.fillText(COLS[i], p, size - margin * 0.42);
      ctx.fillText(String(DIMENSION - i), margin * 0.4, p);
      ctx.fillText(String(DIMENSION - i), size - margin * 0.4, p);
    }

    // 금수 표시
    const stoneSize = step * 0.94;
    if (forbidToggle.checked && IMAGES.f.complete) {
      ctx.globalAlpha = 0.85;
      for (const [x, y] of forbiddenPoints()) {
        const s = step * 0.6;
        ctx.drawImage(IMAGES.f, margin + x * step - s / 2, margin + y * step - s / 2, s, s);
      }
      ctx.globalAlpha = 1;
    }

    // 돌
    for (let x = 0; x < DIMENSION; x++) {
      for (let y = 0; y < DIMENSION; y++) {
        const c = gs.board[x][y];
        if (c !== 'b' && c !== 'w') continue;
        const cx = margin + x * step, cy = margin + y * step;
        ctx.save();
        ctx.shadowColor = 'rgba(0,0,0,0.35)';
        ctx.shadowBlur = step * 0.12;
        ctx.shadowOffsetY = step * 0.05;
        if (IMAGES[c].complete && IMAGES[c].naturalWidth) {
          ctx.drawImage(IMAGES[c], cx - stoneSize / 2, cy - stoneSize / 2, stoneSize, stoneSize);
        } else {
          ctx.fillStyle = c === 'b' ? '#111' : '#fafafa';
          ctx.beginPath(); ctx.arc(cx, cy, stoneSize / 2, 0, Math.PI * 2); ctx.fill();
        }
        ctx.restore();
      }
    }

    // 마지막 수 표시
    const last = gs.moveLog[gs.moveLog.length - 1];
    if (last) {
      const [[x, y], c] = last;
      ctx.strokeStyle = c === 'b' ? '#f4f1e8' : '#1a1a1a';
      ctx.lineWidth = Math.max(1.5, step * 0.07);
      ctx.beginPath();
      ctx.arc(margin + x * step, margin + y * step, step * 0.17, 0, Math.PI * 2);
      ctx.stroke();
    }

    // 승리한 다섯 돌 연결선
    if (winLine) {
      const [a, b] = [winLine[0], winLine[winLine.length - 1]];
      ctx.strokeStyle = css('--win');
      ctx.lineWidth = step * 0.16;
      ctx.lineCap = 'round';
      ctx.globalAlpha = 0.85;
      ctx.beginPath();
      ctx.moveTo(margin + a[0] * step, margin + a[1] * step);
      ctx.lineTo(margin + b[0] * step, margin + b[1] * step);
      ctx.stroke();
      ctx.globalAlpha = 1;
      ctx.lineCap = 'butt';
    }

    // 놓을 자리 미리보기
    if (hover && !thinking && !isOver() && gs.board[hover[0]][hover[1]] === '-') {
      ctx.globalAlpha = 0.45;
      const cx = margin + hover[0] * step, cy = margin + hover[1] * step;
      if (IMAGES.b.complete) ctx.drawImage(IMAGES.b, cx - stoneSize / 2, cy - stoneSize / 2, stoneSize, stoneSize);
      ctx.globalAlpha = 1;
    }
  }

  function pointFromEvent(e) {
    const rect = canvas.getBoundingClientRect();
    const { margin, step } = geometry();
    const x = Math.round((e.clientX - rect.left - margin) / step);
    const y = Math.round((e.clientY - rect.top - margin) / step);
    if (x < 0 || x >= DIMENSION || y < 0 || y >= DIMENSION) return null;
    return [x, y];
  }

  // ---------- 게임 진행 ----------
  function isOver() {
    return gs.blackWin || gs.whiteWin;
  }

  function findWinLine() {
    const last = gs.moveLog[gs.moveLog.length - 1];
    if (!last) return null;
    const [[x, y], c] = last;
    for (const [dx, dy] of [[1, 0], [0, 1], [1, 1], [1, -1]]) {
      const pts = [[x, y]];
      for (const sign of [-1, 1]) {
        let nx = x + sign * dx, ny = y + sign * dy;
        while (nx >= 0 && nx < DIMENSION && ny >= 0 && ny < DIMENSION && gs.board[nx][ny] === c) {
          if (sign < 0) pts.unshift([nx, ny]); else pts.push([nx, ny]);
          nx += sign * dx; ny += sign * dy;
        }
      }
      if (pts.length >= 5) return pts;
    }
    return null;
  }

  function setStatus(text, tone) {
    statusEl.textContent = text;
    statusEl.dataset.tone = tone || '';
  }

  function refresh() {
    forbiddenCache = null;
    winLine = isOver() ? findWinLine() : null;
    const n = gs.moveLog.length;
    moveCountEl.textContent = n;
    const last = gs.moveLog[n - 1];
    lastMoveEl.textContent = last ? `${last[1] === 'b' ? '흑' : '백'} ${label(last[0][0], last[0][1])}` : '없음';
    turnEl.dataset.color = gs.blackToPlay ? 'b' : 'w';
    undoBtn.disabled = thinking || n === 0;
    copyBtn.disabled = n === 0;
    canvas.classList.toggle('busy', thinking);

    logEl.innerHTML = '';
    gs.moveLog.forEach(([[x, y], c], i) => {
      const li = document.createElement('li');
      li.innerHTML = `<span class="num">${i + 1}</span><span class="dot" data-color="${c}"></span>${label(x, y)}`;
      logEl.appendChild(li);
    });
    logEl.scrollTop = logEl.scrollHeight;

    if (gs.blackWin) setStatus('흑 승리! 축하합니다. 새 게임으로 다시 도전해 보세요.', 'win');
    else if (gs.whiteWin) setStatus('백(AI) 승리. 무르기로 되돌려 보거나 새 게임을 시작하세요.', 'lose');
    else if (thinking) setStatus('AI가 생각하는 중입니다...', 'thinking');
    draw();
  }

  async function aiTurn() {
    thinking = true;
    refresh();
    const myRequest = requestId + 1;
    const state = { board: gs.board, moveLog: gs.moveLog, blackToPlay: gs.blackToPlay };
    const res = await askAI(state);
    if (res.id !== myRequest || !thinking) return; // 새 게임/무르기로 취소된 요청
    thinking = false;
    // 반복 심화로 도달한 깊이도 함께 표시 (강제수는 탐색 없이 바로 둠)
    const REASONS = { forced: '강제수', vcf: 'VCF 승리 수순', vct: 'VCT 승리 수순', 'vcf-defense': 'VCF 방어', 'vct-defense': 'VCT 방어' };
    aiTimeEl.textContent = (res.ms / 1000).toFixed(2) + '초 · ' + (REASONS[res.reason] || `깊이 ${res.depth}`);
    if (res.pos) gs.placeStone(res.pos);
    if (!isOver()) setStatus('흑 차례입니다. 교차점을 눌러 돌을 놓으세요.');
    refresh();
  }

  function cancelThinking() {
    if (!thinking) return;
    thinking = false;
    requestId++; // 진행 중인 응답은 무시
    if (worker) {
      worker.terminate();
      try {
        worker = new Worker('ai-worker.js');
      } catch (e) {
        worker = null;
      }
    }
  }

  function playAt(pos) {
    if (thinking || isOver() || !gs.blackToPlay) return;
    const [x, y] = pos;
    if (gs.board[x][y] !== '-') return;
    if (!gs.placeStone(pos)) {
      setStatus(`${label(x, y)}는 금수입니다. 흑은 삼삼, 사사, 장목을 둘 수 없어요.`, 'warn');
      return;
    }
    refresh();
    if (!isOver()) aiTurn();
  }

  function undo() {
    if (gs.moveLog.length === 0) return;
    cancelThinking();
    gs.undoMove();
    // AI 가 둔 수까지 함께 되돌려 다시 흑 차례로 만듦
    if (!gs.blackToPlay) gs.undoMove();
    setStatus('한 수 물렀습니다. 흑 차례입니다.');
    refresh();
  }

  function newGame() {
    cancelThinking();
    gs = new GameState();
    aiTimeEl.textContent = '-';
    setStatus('흑 차례입니다. 교차점을 눌러 첫 수를 두세요.');
    refresh();
  }

  // ---------- 이벤트 ----------
  canvas.addEventListener('click', (e) => {
    const p = pointFromEvent(e);
    if (p) playAt(p);
  });
  canvas.addEventListener('mousemove', (e) => {
    const p = pointFromEvent(e);
    if (String(p) !== String(hover)) { hover = p; draw(); }
  });
  canvas.addEventListener('mouseleave', () => { hover = null; draw(); });
  undoBtn.addEventListener('click', undo);
  newBtn.addEventListener('click', newGame);
  forbidToggle.addEventListener('change', draw);
  copyBtn.addEventListener('click', () => {
    const text = gs.moveLogText();
    const done = () => {
      copyBtn.textContent = '복사됨';
      setTimeout(() => { copyBtn.textContent = '기보 복사'; }, 1500);
    };
    try {
      navigator.clipboard.writeText(text).then(done, () => fallbackCopy(text, done));
    } catch (e) {
      fallbackCopy(text, done);
    }
  });
  function fallbackCopy(text, done) {
    const ta = document.createElement('textarea');
    ta.value = text;
    document.body.appendChild(ta);
    ta.select();
    try { document.execCommand('copy'); done(); } catch (e) { /* 선택된 상태로 둠 */ }
    ta.remove();
  }
  window.addEventListener('keydown', (e) => {
    if (e.target.closest('input, textarea')) return;
    if (e.key === 'z' || e.key === 'Z') undo(); // 원본과 같은 z 키 무르기
  });
  window.addEventListener('resize', resize);
  window.matchMedia('(prefers-color-scheme: dark)').addEventListener?.('change', draw);
  new MutationObserver(draw).observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });

  setStatus('흑 차례입니다. 교차점을 눌러 첫 수를 두세요.');
  resize();
  refresh();
})();
