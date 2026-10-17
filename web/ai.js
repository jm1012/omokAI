/*
 * OmokAI_v2.py 를 JavaScript 로 옮긴 파일
 * ai algorithm v2 + (반복 심화 + Zobrist hash + 증분평가)
 * searching : negamax
 * pruning : alpha-beta pruning
 * evaluation(heuristic) : 돌의 패턴에 따른 점수 부여
 * making candidates : 미리 단순 계산으로 상위 12개 후보를 선정함. 강제수가 있다면 그 수만 탐색
 * iterative deepening : 시간 제한까지 depth = 1,2,3,... 순차적으로 탐색. 마지막 결과를 사용.
 * zobrist hash : 앞서 탐색한 국면의 해시를 저장하고 같은 국면이 나오면 그 값을 사용함.
 * incremental evaluation : 착수점을 포함하는 4 방향의 선만 계산하여 평가점수를 갱신함.
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

  // 공간 점수 가중치
  // 5목을 완성할 수 있는 공간에 있는 돌의 개수마다 이 점수를 부여함. 상대가 4칸 띄워 막으면 이 점수가 없어지므로 위협으로 인지함.
  const POTENTIAL_WEIGHT = 40;

  const DIRECTIONS = [[1, 0], [0, 1], [1, 1], [1, -1]];
  const BOARD_SIZE = 15;
  const MAX_CANDIDATES = 12; // 탐색할 후보수의 최대 개수
  const TIME_LIMIT = 2.0;    // 한 수당 주어지는 탐색 시간 (초)
  const MAX_DEPTH = 12;      // 탐색 최대 깊이

  // 탐색 시간 관리용 전역 변수
  class SearchTimeout extends Error {} // 시간이 다 되면 즉시 탐색 종료 시키기 위한 예외
  let searchDeadline = Infinity; // 이 시각(ms)이 지나면 탐색 중단
  let nodeCount = 0;             // 탐색한 노드 수
  const now = () => (typeof performance !== 'undefined' ? performance.now() : Date.now());

  /*
   * Zobrist hash
   * (칸, 색깔) 마다 랜덤 숫자를 부여 15x15x2 = 450 가지
   * 국면의 해시 = 놓인 돌의 숫자를 전부 xor 한 값, 백 차례이면 ZOBRIST_SIDE 도 xor
   * JS 의 숫자는 53bit 까지만 정확하므로 상위 21bit(hi) + 하위 32bit(lo) 두 개로 나눠서 xor 함
   * Map 의 키는 hi * 2^32 + lo (53bit 정수)
   */
  let seed = 20261012; // 디버깅 쉽게 하기 위해 시드 고정
  function rand32() { // mulberry32
    seed = (seed + 0x6D2B79F5) | 0;
    let t = seed;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return (t ^ (t >>> 14)) >>> 0;
  }
  const ZOBRIST_HI = { b: new Uint32Array(BOARD_SIZE * BOARD_SIZE), w: new Uint32Array(BOARD_SIZE * BOARD_SIZE) };
  const ZOBRIST_LO = { b: new Uint32Array(BOARD_SIZE * BOARD_SIZE), w: new Uint32Array(BOARD_SIZE * BOARD_SIZE) };
  for (let i = 0; i < BOARD_SIZE * BOARD_SIZE; i++) {
    for (const c of ['b', 'w']) {
      ZOBRIST_HI[c][i] = rand32() & 0x1FFFFF;
      ZOBRIST_LO[c][i] = rand32();
    }
  }
  const SIDE_HI = rand32() & 0x1FFFFF; // 차례정보
  const SIDE_LO = rand32();

  // 해시 [hi, lo] 를 Map 키로 변환
  const hashKey = (h) => h[0] * 4294967296 + h[1];

  // 현재 보드의 해시를 처음부터 계산
  function computeHash(gs) {
    let hi = 0, lo = 0;
    for (let x = 0; x < BOARD_SIZE; x++) {
      for (let y = 0; y < BOARD_SIZE; y++) {
        const c = gs.board[x][y];
        if (c === 'b' || c === 'w') {
          hi ^= ZOBRIST_HI[c][x * BOARD_SIZE + y];
          lo = (lo ^ ZOBRIST_LO[c][x * BOARD_SIZE + y]) >>> 0;
        }
      }
    }
    if (!gs.blackToPlay) {
      hi ^= SIDE_HI;
      lo = (lo ^ SIDE_LO) >>> 0;
    }
    return [hi, lo];
  }

  // 돌을 하나 둔 다음 해시 계산
  function nextHash(h, pos, color) {
    const i = pos[0] * BOARD_SIZE + pos[1];
    return [h[0] ^ ZOBRIST_HI[color][i] ^ SIDE_HI, (h[1] ^ ZOBRIST_LO[color][i] ^ SIDE_LO) >>> 0];
  }

  /*
   * 전치표 (transposition table)
   * TT[해시] = [탐색깊이, 점수, 점수종류, 최선수]
   * EXACT : 정확한 값 (alpha < 점수 < beta)
   * LOWER : 하한, 실제 점수 >= 저장된 점수 (beta 이상이라 잘림)
   * UPPER : 상한, 실제 점수 <= 저장된 점수 (alpha를 넘는 수가 없음)
   * CANDIDATE_CACHE[해시] = 후보수 목록 : 같은 국면이면 다시 계산할 필요 없음
   */
  const EXACT = 0, LOWER = 1, UPPER = 2;
  const TT = new Map();
  const CANDIDATE_CACHE = new Map();
  const TT_MAX_SIZE = 500000; // 표가 커지면 메모리가 커지므로 이 값을 초과하면 표를 비움
  let ttHits = 0; // (디버그용) hit 횟수

  function getCandidatesCached(gs, key) {
    let cands = CANDIDATE_CACHE.get(key);
    if (cands === undefined) {
      cands = getCandidateMoves(gs);
      CANDIDATE_CACHE.set(key, cands);
    }
    return cands;
  }

  const samePos = (a, b) => !!a && !!b && a[0] === b[0] && a[1] === b[1];
  const hasPos = (list, p) => !!p && list.some(m => samePos(m, p));

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
  const LINE_CACHE_MAX = 2000000; // 브라우저 메모리 보호용 (캐시라서 비워도 결과는 같음)

  // 좌표 pos 가 몇번째 줄의 몇번째 칸에 위치하는지 저장함 [[줄번호, 칸번호], ...]
  const POS_LINES = [];
  for (let i = 0; i < BOARD_SIZE * BOARD_SIZE; i++) POS_LINES.push([]);
  LINES.forEach((line, idxLine) => {
    line.forEach(([x, y], idxPos) => POS_LINES[x * BOARD_SIZE + y].push([idxLine, idxPos]));
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
  // me  : 내가 pos 에 둔 경우 내 패턴 (전, 후)
  // opp : 상대가 pos 에 둔 경우 상대 패턴 (전, 후), 내가 pos 에 둔 뒤의 상대 패턴
  function analyzeMove(board, pos, color, oppColor) {
    const meBefore = new Array(8).fill(0), meAfter = new Array(8).fill(0);
    const oppBefore = new Array(8).fill(0), oppAfter = new Array(8).fill(0);
    const oppBlocked = new Array(8).fill(0);
    for (const [idxLine, idxPos] of POS_LINES[pos[0] * BOARD_SIZE + pos[1]]) {
      // 증분상태가 있다면 저장된 문자열을 그대로 사용
      const chars = incActive ? incLineStrs[idxLine] : lineString(board, LINES[idxLine]);
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
      // 강제수 (이 자리에 상대가 두면 열린4가 새로 생기는 경우, 흑의 금수는 제외)
      if (oppAfter[1] > oppBefore[1] && !(oppColor === 'b' && gs.getForbiddenMove(pos))) oppOpenFour = true;
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

  // 후보수의 정렬을 위한 단순한 점수 계산 (공간 점수는 가중치 없이 1배로 사용)
  function getSimpleScore(c) {
    return c[0] * WIN_SCORE
      + c[1] * SCORE_TABLE.open4 + c[2] * SCORE_TABLE.closed4
      + c[3] * SCORE_TABLE.open3 + c[4] * SCORE_TABLE.closed3
      + c[5] * SCORE_TABLE.open2 + c[6] * SCORE_TABLE.closed2
      + c[7];
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

  /*
   * 증분평가
   * 돌을 둘 때 착수점을 포함한 4방향의 줄만 변화하므로 해당 줄만 계산함.
   * incLineStrs[줄 번호]   : 그 줄의 현재 문자열
   * incLineCounts[줄 번호] : 그 줄의 현재 패턴 개수 {b, w}
   * incTotals             : 모든 줄의 패턴 개수 합계 (평가점수 계산용)
   * incStack              : 착수하기 전 값을 저장 (무를때 필요)
   * 탐색중 makeMove / unmakeMove 를 함께 사용해야 점수가 정상 유지됨
   */
  const INC_DEBUG = false;
  let incActive = false;
  let incLineStrs = [];
  let incLineCounts = [];
  let incTotals = { b: new Array(8).fill(0), w: new Array(8).fill(0) };
  let incStack = [];

  // 현재 보드에서 증분상태를 새로 계산 (aiMove 실행시 한번 실행)
  function incInit(gs) {
    incLineStrs = LINES.map(line => lineString(gs.board, line));
    incLineCounts = [];
    incTotals = { b: new Array(8).fill(0), w: new Array(8).fill(0) };
    for (const chars of incLineStrs) {
      const counts = { b: countLinePatterns(chars, 'b'), w: countLinePatterns(chars, 'w') };
      incLineCounts.push(counts);
      addCounts(incTotals.b, counts.b);
      addCounts(incTotals.w, counts.w);
    }
    incStack = [];
    incActive = true;
  }

  // pos 에 color 돌을 두었을 때 지나는 줄만 갱신
  function incPlace(pos, color) {
    const saved = [];
    for (const [idxLine, idxPos] of POS_LINES[pos[0] * BOARD_SIZE + pos[1]]) {
      // 착수 이전 문자열과 패턴 개수
      const strBefore = incLineStrs[idxLine];
      const cntBefore = incLineCounts[idxLine];
      // 착수 이후 문자열과 패턴 개수
      const strAfter = strBefore.slice(0, idxPos) + color + strBefore.slice(idxPos + 1);
      const cntAfter = { b: countLinePatterns(strAfter, 'b'), w: countLinePatterns(strAfter, 'w') };
      // 전체 패턴 개수를 갱신
      for (const c of ['b', 'w']) {
        const total = incTotals[c], before = cntBefore[c], after = cntAfter[c];
        for (let i = 0; i < 8; i++) total[i] += after[i] - before[i];
      }
      incLineStrs[idxLine] = strAfter;
      incLineCounts[idxLine] = cntAfter;
      saved.push([idxLine, strBefore, cntBefore]); // 착수전 정보
    }
    incStack.push(saved);
  }

  // 마지막으로 둔 돌을 되돌림
  function incUndo() {
    for (const [idxLine, strBefore, cntBefore] of incStack.pop()) {
      const cntAfter = incLineCounts[idxLine];
      incLineStrs[idxLine] = strBefore;
      incLineCounts[idxLine] = cntBefore;
      for (const c of ['b', 'w']) {
        const total = incTotals[c], before = cntBefore[c], after = cntAfter[c];
        for (let i = 0; i < 8; i++) total[i] += before[i] - after[i];
      }
    }
  }

  // 탐색용 착수 / 무르기 : 보드와 증분 상태를 함께 바꿈
  function makeMove(gs, move) {
    const color = gs.blackToPlay ? 'b' : 'w';
    if (!gs.placeStone(move)) return false; // 착수 불가능
    if (incActive) incPlace(move, color);
    return true;
  }

  function unmakeMove(gs) {
    gs.undoMove();
    if (incActive) incUndo();
  }

  // 증분 상태로 점수 계산
  function evaluateInc(gs) {
    if (!incActive) return evaluate(gs);
    const score = scoreFromCounts(incTotals.b, true) - scoreFromCounts(incTotals.w, false);
    if (INC_DEBUG) {
      const full = evaluate(gs);
      if (score !== full) throw new Error(`증분 평가 불일치 ${score} ${full}`);
    }
    return score;
  }

  // 패턴 개수를 점수로 변환하는 함수
  // counts : [5목, 열린4, 닫힌4, 열린3, 닫힌3, 열린2, 닫힌2, 공간점수]
  function scoreFromCounts(counts, isBlack) {
    const [five, open4, closed4, open3, closed3, open2, closed2, potential] = counts;
    if (five > 0) return WIN_SCORE; // 승리
    let score = open4 * SCORE_TABLE.open4 + closed4 * SCORE_TABLE.closed4
      + open3 * SCORE_TABLE.open3 + closed3 * SCORE_TABLE.closed3
      + open2 * SCORE_TABLE.open2 + closed2 * SCORE_TABLE.closed2
      + potential * POTENTIAL_WEIGHT;
    // 강한 공격 (4,3 이나 4,4 처럼 막을 수 없는 수)
    if (closed4 >= 1 && open3 >= 1) score += SCORE_TABLE.open4; // 4,3 은 열린4 점수를 부여함
    if (closed4 >= 2 && !isBlack) score += SCORE_TABLE.open4;  // 백의 4,4 는 열린4 점수를 부여함
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

    // 공간점수 (5목을 만들 수 있는 5칸 공간 안의 내 돌 개수 합)
    let potential = 0;
    for (let i = 1; i < n - 5; i++) {
      const window = chars.slice(i, i + 5);
      if (window.includes('#')) continue;
      if (isBlack && (chars[i - 1] === 'x' || chars[i + 5] === 'x')) continue; // 흑 장목
      potential += count(window, 'x');
    }

    const result = [
      five,
      open4.size, minus(fours, open4),
      open3.size, minus(threes, open3),
      open2.size, minus(twos, open2),
      potential,
    ];
    if (LINE_CACHE.size >= LINE_CACHE_MAX) LINE_CACHE.clear();
    LINE_CACHE.set(key, result);
    return result;
  }

  /*
   * negamax : 점수를 항상 "지금 둘 차례인 쪽" 기준으로 계산함 (양수 = 차례인 쪽이 유리)
   * depth : 남은 탐색 깊이
   * alpha : 지금 차례인 쪽이 이미 확보한 최선의 점수 (하한)
   * beta  : 상대가 허용하는 최대 점수 (상한). alpha >= beta 이면 더 볼 필요 없음
   * hash  : 해시값 [hi, lo], null 이면 새로 계산함
   */
  function negamax(gs, depth, alpha, beta, hash = null) {
    // 32 노드 마다 시간 확인
    nodeCount++;
    if (nodeCount % 32 === 0 && now() > searchDeadline) throw new SearchTimeout();

    // 승부가 난 노드 = 직전에 상대가 5목을 만든 상태 -> 지금 차례인 쪽은 항상 진 것
    // depth 가 많이 남아 있을수록(= 더 빨리 졌을수록) 더 나쁜 점수 -> 빠른 승리 / 늦은 패배를 선호
    if (gs.blackWin || gs.whiteWin) return [-(WIN_SCORE + depth), null];

    // 전치표 확인
    if (hash === null) hash = computeHash(gs);
    const key = hashKey(hash);
    const alphaOrig = alpha;
    let ttMove = null;
    const entry = TT.get(key); // 깊이, 점수, 타입, 최선수
    if (entry !== undefined) {
      const [eDepth, eScore, eFlag, eMove] = entry;
      ttMove = eMove; // (깊이가 부족해서 점수를 사용하지 못해도) 최선수는 먼저 탐색할 수로 사용
      if (eDepth >= depth) { // 해시의 탐색 깊이가 현재 깊이보다 깊은 경우에만 해시를 사용
        if (eFlag === EXACT) { ttHits++; return [eScore, eMove]; }
        if (eFlag === LOWER) alpha = Math.max(alpha, eScore); // 하한, update alpha
        else beta = Math.min(beta, eScore);                   // 상한, update beta
        if (alpha >= beta) { ttHits++; return [eScore, eMove]; } // 저장된 경계값만으로 잘라내기 가능
      }
    }

    // 평가함수는 흑 기준이므로 백 차례이면 부호를 뒤집음
    if (depth === 0) {
      const score = evaluateInc(gs);
      return [gs.blackToPlay ? score : -score, null];
    }

    let candidates = getCandidatesCached(gs, key); // 같은 국면이면 후보수를 다시 계산하지 않음
    if (!candidates.length) {
      const score = evaluateInc(gs);
      return [gs.blackToPlay ? score : -score, null];
    }

    // 전치표에 저장된 최선수를 가장 먼저 탐색함 (가지치기 강화)
    if (hasPos(candidates, ttMove) && !samePos(candidates[0], ttMove)) {
      candidates = [ttMove, ...candidates.filter(m => !samePos(m, ttMove))];
    }

    const color = gs.blackToPlay ? 'b' : 'w'; // hash 갱신용
    let bestScore = -Infinity;
    let bestPos = null;
    for (const move of candidates) {
      // 착수에 실패하면(금수 등) undoMove 가 직전 수를 지우지 않도록 건너뜀
      if (!makeMove(gs, move)) continue;
      let score;
      // 탐색 도중 시간초과 시 이미 착수한 돌은 반드시 되돌려야함
      try {
        [score] = negamax(gs, depth - 1, -beta, -alpha, nextHash(hash, move, color));
      } finally {
        unmakeMove(gs);
      }
      score = -score; // 상대 기준 점수 -> 내 기준 점수
      // 같은 점수면 먼저 본 수를 유지 (가지치기로 잘린 수는 점수가 경계값이므로)
      if (!bestPos || score > bestScore) {
        bestScore = score;
        bestPos = move;
      }
      alpha = Math.max(alpha, score);
      if (alpha >= beta) break;
    }

    // 결과를 전치표에 저장
    if (bestPos) {
      let flag;
      if (bestScore <= alphaOrig) flag = UPPER;   // alpha 보다 큰 수가 없었음, 실제 점수는 이것 이하
      else if (bestScore >= beta) flag = LOWER;   // beta 이상이라 잘림, 실제 점수는 이것 이상
      else flag = EXACT;
      TT.set(key, [depth, bestScore, flag, bestPos]);
    }
    return [bestScore, bestPos];
  }

  // 루트탐색: 이전 탐색의 최선 수를 후보수의 가장 앞에 배치함
  function searchRoot(gs, depth, candidates, firstMove, hash) {
    if (hasPos(candidates, firstMove)) {
      candidates = [firstMove, ...candidates.filter(m => !samePos(m, firstMove))];
    }
    const color = gs.blackToPlay ? 'b' : 'w';
    let alpha = -Infinity;
    const beta = Infinity;
    let bestScore = -Infinity;
    let bestPos = null;
    for (const move of candidates) {
      if (!makeMove(gs, move)) continue;
      let score;
      try {
        [score] = negamax(gs, depth - 1, -beta, -alpha, nextHash(hash, move, color));
      } finally {
        unmakeMove(gs);
      }
      score = -score;
      if (!bestPos || score > bestScore) {
        bestScore = score;
        bestPos = move;
      }
      alpha = Math.max(alpha, score);
    }
    return [bestScore, bestPos];
  }

  // ai 착수 (반복 심화). opts.timeLimit(초), opts.maxDepth 로 바꿀 수 있음 (테스트용)
  function aiMove(gs, opts = {}) {
    const timeLimit = opts.timeLimit ?? TIME_LIMIT;
    const maxDepth = opts.maxDepth ?? MAX_DEPTH;
    if (gs.moveLog.length === 0) return { pos: [7, 7], score: 0, depth: 0, nodes: 0, forced: true }; // 첫 수는 중앙

    nodeCount = 0;
    ttHits = 0;
    const startTime = now();

    // 전치표는 다음수에서 재사용, 크기 초과시 초기화
    if (TT.size > TT_MAX_SIZE) TT.clear();
    if (CANDIDATE_CACHE.size > TT_MAX_SIZE) CANDIDATE_CACHE.clear();
    const hash = computeHash(gs);

    // 후보수
    const candidates = getCandidateMoves(gs);
    if (!candidates.length) return { pos: null, score: 0, depth: 0, nodes: 0 };
    if (candidates.length === 1) { // 강제수가 하나이면 탐색하지 않아도 됨
      return { pos: candidates[0], score: 0, depth: 0, nodes: 0, forced: true };
    }

    // 탐색
    incInit(gs); // 현재 보드로 증분상태 만들기
    let bestScore = 0, bestPos = candidates[0], reachedDepth = 0;
    try {
      for (let depth = 1; depth <= maxDepth; depth++) {
        searchDeadline = depth === 1 ? Infinity : startTime + timeLimit * 1000; // 시작시각+제한시간
        let score, pos;
        try {
          [score, pos] = searchRoot(gs, depth, candidates, bestPos, hash);
        } catch (e) {
          if (e instanceof SearchTimeout) break; // 탐색 중간에 타임아웃 시 결과를 버림
          throw e;
        }
        if (pos) {
          bestScore = score;
          bestPos = pos;
          reachedDepth = depth;
        }
        // 이기거나 지는 수순 발견 시 더 이상 탐색하지 않음
        if (Math.abs(bestScore) >= WIN_SCORE) break;
        // 다음 탐색을 시간 내에 못 끝낼 가능성이 매우 높으므로 탐색을 미리 중단함
        if (now() - startTime > timeLimit * 1000 / 2) break;
      }
    } finally {
      // 탐색 종료시 증분상태 종료
      incActive = false;
    }

    const blackScore = gs.blackToPlay ? bestScore : -bestScore;
    return { pos: bestPos, score: blackScore, depth: reachedDepth, nodes: nodeCount, ttHits };
  }

  // 캐시를 모두 비움 (테스트용)
  function resetCaches() {
    TT.clear();
    CANDIDATE_CACHE.clear();
    LINE_CACHE.clear();
  }

  // 판 상태(board, moveLog, blackToPlay)로 GameState 를 다시 만듦
  function restore(state) {
    const gs = new GameState();
    gs.board = state.board.map(row => row.slice());
    gs.moveLog = state.moveLog.map(([p, c]) => [p.slice(), c]);
    gs.blackToPlay = state.blackToPlay;
    return gs;
  }

  root.OmokAI = {
    aiMove, negamax, searchRoot, evaluate, evaluateInc, incInit, getCandidateMoves,
    countLinePatterns, computeHash, restore, resetCaches, TIME_LIMIT, MAX_DEPTH,
  };
  if (typeof module !== 'undefined') module.exports = root.OmokAI;

  // Web Worker 로 실행된 경우: 판을 받아 계산한 착수점을 돌려줌
  if (typeof WorkerGlobalScope !== 'undefined' && root instanceof WorkerGlobalScope) {
    root.onmessage = (e) => {
      const { id, state } = e.data;
      const t0 = now();
      const res = aiMove(restore(state));
      root.postMessage({ id, ...res, ms: now() - t0 });
    };
  }
})(typeof self !== 'undefined' ? self : globalThis);
