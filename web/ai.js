/*
 * OmokAI_v2.py 를 JavaScript 로 옮긴 파일
 * searching : negamax
 * pruning : alpha-beta pruning
 * 후보수 선정 : 강제수 + 수 정렬 + 후보수 축소
 * Web Worker 안에서 실행되면 메시지로 판을 받아 착수점을 돌려줌
 */
(function (root) {
  const { GameState, count } = root.OmokEngine;

  const SCORE_TABLE = {
    open4: 100000,  // 열린 사
    closed4: 10000, // 닫힌 사
    open3: 1000,    // 열린 삼
    closed3: 100,   // 닫힌 삼
    open2: 50,      // 열린 두
    closed2: 10,    // 닫힌 두
  };

  const WIN_SCORE = 1000000; // 승리점수
  const DIRECTIONS = [[1, 0], [0, 1], [1, 1], [1, -1]];
  const BOARD_SIZE = 15;
  const MAX_CANDIDATES = 12; // 탐색할 후보수의 최대 개수
  let AI_DEPTH = 5;          // 탐색의 최대 깊이

  // 보드의 모든 줄(가로, 세로, 대각선 2개)의 좌표 목록을 미리 만들어 둠
  // 길이가 5 미만인 대각선은 5목이 나올 수 없으므로 제외
  function makeLines(size) {
    const lines = [];
    for (const [dx, dy] of DIRECTIONS) {
      for (let x = 0; x < size; x++) {
        for (let y = 0; y < size; y++) {
          // 줄의 시작점: 한 칸 뒤가 보드 밖인 좌표
          if (0 <= x - dx && x - dx < size && 0 <= y - dy && y - dy < size) continue;
          const line = [];
          let cx = x, cy = y;
          while (0 <= cx && cx < size && 0 <= cy && cy < size) {
            line.push([cx, cy]);
            cx += dx;
            cy += dy;
          }
          if (line.length >= 5) lines.push(line);
        }
      }
    }
    return lines;
  }
  const LINES = makeLines(BOARD_SIZE);
  const LINE_CACHE = new Map(); // 속도 개선용, 변화가 없는 줄은 저장해 두고 사용

  // 좌표 pos 가 몇번째 줄의 몇번째 칸에 위치하는지 저장함 [[줄번호, 칸번호], ...]
  const POS_LINES = new Map();
  LINES.forEach((line, idxLine) => {
    line.forEach(([x, y], idxPos) => {
      const key = x * BOARD_SIZE + y;
      if (!POS_LINES.has(key)) POS_LINES.set(key, []);
      POS_LINES.get(key).push([idxLine, idxPos]);
    });
  });

  function lineString(board, line) {
    let s = '';
    for (const [x, y] of line) s += board[x][y];
    return s;
  }

  function addCounts(total, counts) {
    for (let i = 0; i < 8; i++) total[i] += counts[i];
  }

  // pos 기준 패턴을 추출하는 함수, 후보수 정렬 및 후보수 축소를 위한 함수
  function analyzeMove(board, pos, color, oppColor) {
    const meBefore = new Array(8).fill(0), meAfter = new Array(8).fill(0);
    const oppBefore = new Array(8).fill(0), oppAfter = new Array(8).fill(0);
    const oppBlocked = new Array(8).fill(0);
    for (const [idxLine, idxPos] of POS_LINES.get(pos[0] * BOARD_SIZE + pos[1]) || []) {
      const chars = lineString(board, LINES[idxLine]);
      const myLine = chars.slice(0, idxPos) + color + chars.slice(idxPos + 1);
      const oppLine = chars.slice(0, idxPos) + oppColor + chars.slice(idxPos + 1);
      addCounts(meBefore, countLinePatterns(chars, color));
      addCounts(meAfter, countLinePatterns(myLine, color));
      addCounts(oppBefore, countLinePatterns(chars, oppColor));
      addCounts(oppAfter, countLinePatterns(oppLine, oppColor));
      addCounts(oppBlocked, countLinePatterns(myLine, oppColor));
    }
    return [meBefore, meAfter, oppBefore, oppAfter, oppBlocked];
  }

  // 탐색수를 줄이기 위한 후보수 선정, radius 범위 이내의 좌표를 후보로 정함
  function getCandidateMoves(gs, radius = 2) {
    // ai가 두번째 수는 첫 수에 붙여서 두도록 제한함.
    if (gs.moveLog.length === 1) radius = 1;
    const n = gs.board.length;
    const seen = new Uint8Array(n * n);
    for (let x = 0; x < n; x++) {
      for (let y = 0; y < n; y++) {
        if (gs.board[x][y] === '-') continue;
        for (let nx = x - radius; nx <= x + radius; nx++) {
          for (let ny = y - radius; ny <= y + radius; ny++) {
            if (0 <= nx && nx < n && 0 <= ny && ny < n && gs.board[nx][ny] === '-') seen[nx * n + ny] = 1;
          }
        }
      }
    }
    // 중복 제거 (좌표 순서로 정렬된 목록)
    let candidates = [];
    for (let i = 0; i < n * n; i++) if (seen[i]) candidates.push([Math.floor(i / n), i % n]);

    // 흑차례이면 금수는 고려하지 않음 (금수 제거)
    if (gs.blackToPlay) {
      candidates = candidates.filter(p => !(gs.getForbiddenMove(p) && !gs.isWin(p)));
    }

    const color = gs.blackToPlay ? 'b' : 'w';
    const oppColor = gs.blackToPlay ? 'w' : 'b';
    const myWins = [];  // 내가 오목을 만들 수 있는 수
    const oppWins = []; // 상대가 오목을 만들 수 있는 수
    let oppOpenFour = false; // 상대가 다음수에 열린사를 만들수 있는지 여부
    let scored = [];

    for (const pos of candidates) {
      const [meBefore, meAfter, oppBefore, oppAfter, oppBlocked] = analyzeMove(gs.board, pos, color, oppColor);
      // 강제수 (오목을 완성하는 경우)
      if (meAfter[0] > 0) myWins.push(pos);
      if (oppAfter[0] > 0) oppWins.push(pos);
      // 강제수 (상대가 사목을 만들 수 있는 경우 (삼목), 흑의 금수는 제외)
      if (oppAfter[1] > 0 && !(oppColor === 'b' && gs.getForbiddenMove(pos))) oppOpenFour = true;
      // 후보수 정렬 (착수점 기준 점수 부여, 사를 만드는 수, 공격을 막는 수)
      const isMakingFour = meAfter[1] + meAfter[2] > meBefore[1] + meBefore[2];
      const isBlocking = oppBlocked[3] < oppBefore[3] || oppBlocked[2] < oppBefore[2] || oppBlocked[1] < oppBefore[1];
      const score = (getSimpleScore(meAfter) - getSimpleScore(meBefore)) + (getSimpleScore(oppAfter) - getSimpleScore(oppBefore));
      scored.push([score, pos, isMakingFour, isBlocking]);
    }

    // 내가 이기는 수가 있으면 그 수만 탐색함
    if (myWins.length) return myWins.slice(0, 1);
    // 상대가 이기는 수가 있으면 막는 수만 탐색
    if (oppWins.length) return oppWins;
    // 상대가 열린삼이 있으면 막는 수 또는 사를 만드는 수 만 탐색
    if (oppOpenFour) {
      const forcedMove = scored.filter(m => m[2] || m[3]);
      if (forcedMove.length) scored = forcedMove;
    }

    // 점수가 높은 순서로 정렬 (같은 점수는 원래 순서 유지), 상위 MAX_CANDIDATES 개만 탐색함
    scored.sort((a, b) => b[0] - a[0]);
    return scored.slice(0, MAX_CANDIDATES).map(m => m[1]);
  }

  // 후보수의 정렬을 위한 단순한 점수 계산
  function getSimpleScore(c) {
    return c[0] * WIN_SCORE
      + c[1] * SCORE_TABLE.open4 + c[2] * SCORE_TABLE.closed4
      + c[3] * SCORE_TABLE.open3 + c[4] * SCORE_TABLE.closed3
      + c[5] * SCORE_TABLE.open2 + c[6] * SCORE_TABLE.closed2;
  }

  // 평가함수. 현재 보드의 점수를 흑 기준으로 계산
  // 모든 줄을 문자열로 읽음 -> 패턴 추출 -> SCORE_TABLE 으로 점수 부여
  function evaluate(gs) {
    const board = gs.board;
    const counts = { b: new Array(8).fill(0), w: new Array(8).fill(0) };
    for (const line of LINES) {
      const chars = lineString(board, line);
      const hasB = chars.includes('b'), hasW = chars.includes('w');
      if (!hasB && !hasW) continue; // 빈 줄은 건너뛰기
      if (hasB) addCounts(counts.b, countLinePatterns(chars, 'b'));
      if (hasW) addCounts(counts.w, countLinePatterns(chars, 'w'));
    }
    return scoreFromCounts(counts.b, true) - scoreFromCounts(counts.w, false);
  }

  // 패턴 개수를 점수로 변환하는 함수
  // counts : [5목, 열린4, 닫힌4, 열린3, 닫힌3, 열린2, 닫힌2, -]
  function scoreFromCounts(counts, isBlack) {
    const [five, open4, closed4, open3, closed3, open2, closed2] = counts;
    if (five > 0) return WIN_SCORE; // 승리
    // 점수 계산 (원본의 closed3, closed2 자리에 closed4 가 들어가 있던 오타 수정)
    let score = open4 * SCORE_TABLE.open4 + closed4 * SCORE_TABLE.closed4
      + open3 * SCORE_TABLE.open3 + closed3 * SCORE_TABLE.closed3
      + open2 * SCORE_TABLE.open2 + closed2 * SCORE_TABLE.closed2;
    // 강한 공격 (4,3 이나 4,4 처럼 막을 수 없는 수)
    if (open4 >= 1 && open3 >= 1) score += SCORE_TABLE.open4; // 4,3 은 열린4 점수를 부여함
    if (closed4 >= 2 && !isBlack) score += SCORE_TABLE.open4; // 백의 4,4 는 열린4 점수를 부여함
    return score;
  }

  /*
   * 한 라인에서 패턴의 개수를 세는 함수, 결과는 LINE_CACHE 에 저장함
   * 내 돌 = 'x', 빈 칸 = '-', 상대 돌과 벽 = '#'
   * 돌 위치 묶음은 "1,2,3" 같은 문자열로 저장해 집합 연산에 사용
   */
  function countLinePatterns(line, color) {
    const key = color + line;
    const cached = LINE_CACHE.get(key);
    if (cached) return cached;

    const isBlack = color === 'b';
    let chars = '#';
    for (const ch of line) chars += ch === color ? 'x' : (ch === '-' ? '-' : '#');
    chars += '#';
    const n = chars.length;

    // 5칸 윈도우 안에 돌 k개 + 나머지 빈칸 -> 돌 위치를 묶음 (중복 카운트 방지)
    function stoneSets(k) {
      const result = new Map();
      for (let i = 1; i < n - 5; i++) {
        const window = chars.slice(i, i + 5);
        if (window.includes('#') || count(window, 'x') !== k) continue;
        if (isBlack && (chars[i - 1] === 'x' || chars[i + 5] === 'x')) continue; // 흑의 장목 처리
        const stones = [];
        for (let j = i; j < i + 5; j++) if (chars[j] === 'x') stones.push(j);
        result.set(stones.join(','), stones);
      }
      return result;
    }

    // 열린 4 '-xxxx-' 위치 반환 함수
    function openFourStones(t) {
      const result = new Map();
      let start = t.indexOf('-xxxx-');
      while (start !== -1) {
        const before = start - 1 >= 0 ? t[start - 1] : '#';
        const after = start + 6 < t.length ? t[start + 6] : '#';
        if (!(isBlack && (before === 'x' || after === 'x'))) {
          const stones = [start + 1, start + 2, start + 3, start + 4];
          result.set(stones.join(','), stones);
        }
        start = t.indexOf('-xxxx-', start + 1);
      }
      return result;
    }

    // 5목
    let five = 0;
    for (let i = 1; i < n - 4; i++) {
      if (chars.slice(i, i + 5) === 'xxxxx') {
        if (isBlack && (chars[i - 1] === 'x' || chars[i + 5] === 'x')) continue; // 흑의 장목 처리
        five = 1;
        break;
      }
    }

    // 4목
    const fours = stoneSets(4);
    const open4 = openFourStones(chars);

    // 3목
    // 열린 삼 (돌을 하나 더 두었을 때 열린 4가 되는 3개의 돌)
    let open3 = new Map();
    if (count(chars, 'x') >= 3) {
      for (let i = 1; i < n - 1; i++) {
        if (chars[i] !== '-') continue;
        const tmp = chars.slice(0, i) + 'x' + chars.slice(i + 1); // 좌표 i 에 돌을 하나 둬 봄
        for (const stones of openFourStones(tmp).values()) {
          if (stones.includes(i)) {
            const three = stones.filter(j => j !== i); // 열린 삼 좌표는 열린 사 에서 i 돌을 뺀 것
            open3.set(three.join(','), three);
          }
        }
      }
    }
    let threes = stoneSets(3);

    // 2목
    // 열린 2 (6칸 윈도우에서 양 끝이 빈칸이고, 돌2개 빈칸 2개인 경우)
    let twos = stoneSets(2);
    let open2 = new Map();
    for (let i = 0; i < n - 5; i++) {
      const window = chars.slice(i, i + 6);
      if (window[0] !== '-' || window[5] !== '-' || window.includes('#') || count(window, 'x') !== 2) continue;
      const stones = [];
      for (let j = i; j < i + 6; j++) if (chars[j] === 'x') stones.push(j);
      open2.set(stones.join(','), stones);
    }
    open2 = new Map([...open2].filter(([k]) => twos.has(k)));

    // 큰 패턴의 일부인 작은 패턴은 중복으로 세지 않음
    function notInside(small, bigs) {
      const result = new Map();
      for (const [k, a] of small) {
        let inside = false;
        for (const b of bigs) {
          if (a.every(v => b.includes(v))) { inside = true; break; }
        }
        if (!inside) result.set(k, a);
      }
      return result;
    }
    const union = (...maps) => {
      const m = new Map();
      for (const x of maps) for (const [k, v] of x) m.set(k, v);
      return m;
    };
    const minus = (a, b) => [...a.keys()].filter(k => !b.has(k)).length;

    const bigFours = [...union(fours, open4).values()];
    open3 = notInside(open3, bigFours);
    threes = notInside(threes, bigFours);
    const bigThrees = [...union(fours, open4, threes, open3).values()];
    twos = notInside(twos, bigThrees);
    open2 = notInside(open2, bigThrees);

    const result = [
      five,
      open4.size, minus(fours, open4),
      open3.size, minus(threes, open3),
      open2.size, minus(twos, open2),
      0,
    ];
    LINE_CACHE.set(key, result);
    return result;
  }

  /*
   * negamax: 지금 차례인 쪽 기준의 점수를 반환
   * alpha : 내가 보장받은 최선의 값, beta : 상대가 허용하는 최대값
   * alpha >= beta 라면 상대는 이 선택을 하지 않음 -> 탐색하지 않음
   */
  function negamax(gs, depth, alpha, beta) {
    // 승부가 난 노드 = 직전에 상대가 5목을 만든 상태 -> 지금 차례인 쪽은 항상 진 것
    // depth 가 많이 남아 있을수록(= 더 빨리 졌을수록) 더 나쁜 점수 -> 빠른 승리 / 늦은 패배를 선호
    if (gs.blackWin || gs.whiteWin) return [-(WIN_SCORE + depth), null];

    // 평가함수는 흑 기준이므로 백 차례이면 부호를 뒤집음
    if (depth === 0) {
      const score = evaluate(gs);
      return [gs.blackToPlay ? score : -score, null];
    }

    const candidates = getCandidateMoves(gs);
    if (!candidates.length) {
      const score = evaluate(gs);
      return [gs.blackToPlay ? score : -score, null];
    }

    let bestScore = -Infinity;
    let bestPos = null;
    for (const move of candidates) {
      // 착수에 실패하면(금수 등) undoMove 가 직전 수를 지우지 않도록 건너뜀
      if (!gs.placeStone(move)) continue;
      let [score] = negamax(gs, depth - 1, -beta, -alpha);
      score = -score; // 상대 기준 점수 -> 내 기준 점수
      gs.undoMove();
      // 같은 점수면 먼저 본 수를 유지 (가지치기로 잘린 수는 점수가 경계값이므로)
      if (!bestPos || score > bestScore) {
        bestScore = score;
        bestPos = move;
      }
      alpha = Math.max(alpha, score);
      if (alpha >= beta) break;
    }
    return [bestScore, bestPos];
  }

  // ai 착수 (원본의 minimax 호출을 negamax 로 수정)
  function aiMove(gs, depth = AI_DEPTH) {
    const [score, pos] = negamax(gs, depth, -Infinity, Infinity);
    return { pos, score };
  }

  // 판 상태(board, moveLog, blackToPlay)로 GameState 를 다시 만듦
  function restore(state) {
    const gs = new GameState();
    gs.board = state.board.map(row => row.slice());
    gs.moveLog = state.moveLog.map(([p, c]) => [p.slice(), c]);
    gs.blackToPlay = state.blackToPlay;
    return gs;
  }

  root.OmokAI = { aiMove, negamax, evaluate, getCandidateMoves, countLinePatterns, restore, AI_DEPTH };
  if (typeof module !== 'undefined') module.exports = root.OmokAI;

  // Web Worker 로 실행된 경우: 판을 받아 계산한 착수점을 돌려줌
  if (typeof WorkerGlobalScope !== 'undefined' && root instanceof WorkerGlobalScope) {
    root.onmessage = (e) => {
      const { id, state, depth } = e.data;
      const t0 = Date.now();
      const { pos, score } = aiMove(restore(state), depth || AI_DEPTH);
      root.postMessage({ id, pos, score, ms: Date.now() - t0 });
    };
  }
})(typeof self !== 'undefined' ? self : globalThis);
