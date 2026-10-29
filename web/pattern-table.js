/*
 * PatternTable.py 를 JavaScript 로 옮긴 파일
 * 패턴 테이블
 * 칸 하나 x 방향 하나 마다, 그 칸 주변 +-7 칸(14칸)의 상태를 정수 하나(코드)로 저장한다.
 * 칸 상태 : 0 빈칸, 1 흑, 2 백, 3 벽(보드 밖)  -> 2비트씩 14칸 = 28비트
 * TABLE[차례][코드] = 그 칸에 차례인 쪽이 두었을 때의 패턴 변화 (한 번 계산하면 저장)
 * codes 는 Int32Array(15 * 15 * 4), codes[(x * 15 + y) * 4 + d] 가 칸 (x,y), 방향 d 의 코드
 */
(function (root) {
  const DIRECTIONS = [[1, 0], [0, 1], [1, 1], [1, -1]]; // OmokAI 와 같은 순서여야 함
  const BOARD_SIZE = 15;
  let countLinePatterns = null; // setup() 으로 OmokAI 의 함수를 받아옴

  function setup(countFn) {
    countLinePatterns = countFn;
  }

  const RADIUS = 7; // 6 이하로 줄이면 열린 2/3 판정이 창 끝에서 잘려 결과가 달라짐
  const OFFSETS = [];
  for (let k = -RADIUS; k <= RADIUS; k++) if (k !== 0) OFFSETS.push(k); // -7..-1, 1..7
  const SLOT = {}; // 오프셋 -> 비트 위치(0~13)
  OFFSETS.forEach((k, i) => { SLOT[k] = i; });
  const VAL = { '-': 0, b: 1, w: 2 };
  const CH = '-bw#';

  const idx = (x, y, d) => (x * BOARD_SIZE + y) * 4 + d;

  // 모든 칸, 모든 방향의 코드를 계산
  function initCodes(board) {
    const codes = new Int32Array(BOARD_SIZE * BOARD_SIZE * 4);
    for (let x = 0; x < BOARD_SIZE; x++) {
      for (let y = 0; y < BOARD_SIZE; y++) {
        DIRECTIONS.forEach(([dx, dy], d) => {
          let c = 0;
          for (const k of OFFSETS) {
            const nx = x + dx * k, ny = y + dy * k;
            const v = (0 <= nx && nx < BOARD_SIZE && 0 <= ny && ny < BOARD_SIZE) ? VAL[board[nx][ny]] : 3;
            c |= v << (2 * SLOT[k]);
          }
          codes[idx(x, y, d)] = c;
        });
      }
    }
    return codes;
  }

  // (x,y) 에 color 를 두거나(place) 무를 때(undo) 주변 코드 갱신 : 빈칸(0) <-> 돌(1,2) 이므로 xor 하나면 됨
  function updateCodes(codes, pos, color) {
    const [x, y] = pos;
    const v = VAL[color];
    DIRECTIONS.forEach(([dx, dy], d) => {
      for (const k of OFFSETS) {
        const nx = x - dx * k, ny = y - dy * k; // (nx,ny) 에서 보면 pos 는 오프셋 +k 위치
        if (0 <= nx && nx < BOARD_SIZE && 0 <= ny && ny < BOARD_SIZE) codes[idx(nx, ny, d)] ^= v << (2 * SLOT[k]);
      }
    });
  }

  function windowStr(code, center) {
    let left = '', right = '';
    for (const k of OFFSETS) {
      const ch = CH[(code >> (2 * SLOT[k])) & 3];
      if (k < 0) left += ch;
      else right += ch;
    }
    return left + center + right;
  }

  const sub = (a, b) => a.map((v, i) => v - b[i]);

  // 표의 한 칸 계산 : 기존 countLinePatterns 를 그대로 재사용함 (규칙이 같아야 하므로)
  function computeEntry(code, me) {
    const opp = me === 'b' ? 'w' : 'b';
    const before = windowStr(code, '-');
    const mine = windowStr(code, me);
    const theirs = windowStr(code, opp);
    const meDelta = sub(countLinePatterns(mine, me), countLinePatterns(before, me));        // 내가 두면 생기는 내 패턴
    const oppDelta = sub(countLinePatterns(theirs, opp), countLinePatterns(before, opp));  // 상대가 두면 생기는 상대 패턴
    const oppLoss = sub(countLinePatterns(mine, opp), countLinePatterns(before, opp));     // 내가 두면 줄어드는 상대 패턴
    // 흑 장목 : 가운데를 포함한 연속 흑돌이 6개 이상
    let run = 1;
    for (const step of [-1, 1]) {
      let k = step;
      while (-RADIUS <= k && k <= RADIUS && ((code >> (2 * SLOT[k])) & 3) === 1) {
        run++;
        k += step;
      }
    }
    const overline = me === 'b' && run >= 6;
    return [meDelta, oppDelta, oppLoss, overline];
  }

  const TABLE = { b: new Map(), w: new Map() }; // 처음 보는 코드만 계산하고 저장 (지연 생성)

  function lookup(code, me) {
    const t = TABLE[me];
    let e = t.get(code);
    if (e === undefined) {
      e = computeEntry(code, me);
      t.set(code, e);
    }
    return e;
  }

  // 흑 금수 판정 (표 이용)
  function isForbiddenByTable(codes, pos) {
    const [x, y] = pos;
    let threes = 0, fours = 0;
    for (let d = 0; d < 4; d++) {
      const [meDelta, , , overline] = lookup(codes[idx(x, y, d)], 'b');
      if (meDelta[0] > 0) return false; // 오목이 되면 금수 아님
      if (overline) return true;
      if (meDelta[3] > 0) threes++;
      fours += Math.max(0, meDelta[1] + meDelta[2]);
    }
    return threes >= 2 || fours >= 2;
  }

  root.PatternTable = { setup, initCodes, updateCodes, windowStr, lookup, isForbiddenByTable, TABLE, RADIUS, idx };
  if (typeof module !== 'undefined') module.exports = root.PatternTable;
})(typeof self !== 'undefined' ? self : globalThis);
