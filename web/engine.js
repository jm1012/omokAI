/*
 * OmokEngine.py 를 JavaScript 로 옮긴 파일
 * 게임 상태 저장, 착수, 무르기, 승리 판정, 금수(33, 44, 장목) 판정
 * board[x][y] : '-' 빈칸, 'b' 흑, 'w' 백
 */
(function (root) {
  const DIRECTIONS = [[1, 0], [0, 1], [1, 1], [1, -1]];

  class GameState {
    constructor() {
      this.board = [];
      for (let x = 0; x < 15; x++) this.board.push(new Array(15).fill('-'));
      this.blackToPlay = true;
      this.whiteWin = false;
      this.blackWin = false;
      this.moveLog = []; // [[x, y], color]
    }

    inBoard(x, y) {
      return 0 <= x && x < this.board.length && 0 <= y && y < this.board[x].length;
    }

    placeStone(pos) {
      const [x, y] = pos;
      if (!this.inBoard(x, y)) return false;
      if (this.board[x][y] !== '-') return false;

      // 승리 판정
      if (this.isWin(pos)) {
        if (this.blackToPlay) this.blackWin = true;
        else this.whiteWin = true;
        this.board[x][y] = this.blackToPlay ? 'b' : 'w';
        // ai 를 위한 로그 추가, 턴 바꾸기
        this.moveLog.push([[x, y], this.board[x][y]]);
        this.blackToPlay = !this.blackToPlay;
        return true;
      }

      // 흑 차례이면 금수 판정 함수를 호출, 금수인 경우 착수 금지
      if (this.blackToPlay && this.getForbiddenMove(pos)) return false;

      // 착수, 턴 교대
      this.board[x][y] = this.blackToPlay ? 'b' : 'w';
      this.blackToPlay = !this.blackToPlay;
      this.moveLog.push([[x, y], this.board[x][y]]);
      return true;
    }

    undoMove() {
      if (this.moveLog.length === 0) return;
      const [pos] = this.moveLog.pop();
      this.board[pos[0]][pos[1]] = '-';
      this.blackToPlay = !this.blackToPlay;
      this.blackWin = false;
      this.whiteWin = false;
    }

    isWin(pos) {
      const [x, y] = pos;
      const currentPlayer = this.blackToPlay ? 'b' : 'w';
      if (!this.inBoard(x, y)) return false;
      if (this.board[x][y] !== '-') return false;
      for (const [dx, dy] of DIRECTIONS) {
        let stoneCount = 1;
        for (const sign of [-1, 1]) { // 양 방향으로 탐색함
          let nx = x + sign * dx;
          let ny = y + sign * dy;
          while (this.inBoard(nx, ny) && this.board[nx][ny] === currentPlayer) {
            stoneCount++;
            nx += sign * dx;
            ny += sign * dy;
          }
        }
        if (currentPlayer === 'b' && stoneCount === 5) return true; // 흑은 정확히 5개의 돌인 경우 승리
        if (currentPlayer === 'w' && stoneCount >= 5) return true;  // 백은 6목 이상도 허용
      }
      return false;
    }

    // 금수 판정, 흑돌의 경우 33, 44, 장목이 금지됨
    getForbiddenMove(pos) {
      return this.isDoubleThree(pos) || this.isDoubleFour(pos) || this.isOverLine(pos);
    }

    // 삼삼 금수
    isDoubleThree(pos) {
      const [x, y] = pos;
      if (!this.inBoard(x, y) || this.board[x][y] !== '-') return false;
      let doubleThreePossible = false;
      for (const [dx, dy] of DIRECTIONS) {
        if (this.isOpenThree(x, y, dx, dy)) {
          if (!doubleThreePossible) doubleThreePossible = true;
          else return true;
        }
      }
      return false;
    }

    // 열린 삼 판정, 흑돌 하나를 두었을 때 열린 사가 되면 열린 삼
    isOpenThree(x, y, dx, dy) {
      let chars = this.getLinePattern(x, y, dx, dy, 6); // 길이 13
      const c = Math.floor(chars.length / 2);
      chars = chars.slice(0, c) + 'b' + chars.slice(c + 1); // 중앙에 흑돌을 두었다고 가정
      for (let i = 0; i < chars.length; i++) {
        if (chars[i] !== '-') continue;
        const tmp = chars.slice(0, i) + 'b' + chars.slice(i + 1); // 빈칸에 흑돌을 하나 두어 봄
        for (let j = 0; j < chars.length - 5; j++) {
          // "열린 사"이면서, 착수점이 포함인 경우 열린 삼 판정
          if (tmp.slice(j, j + 6) !== '-bbbb-') continue;
          if (!(j < c && c < j + 6)) continue;
          // 새로 둔 돌 i 가 열린 사에 포함되어야 함 (이미 열린 사인 줄은 삼이 아님)
          if (!(j < i && i < j + 5)) continue;
          // 열린 사가 아닌 경우 확인 (장목이 되는 경우)
          const beforeTmp = j - 1 >= 0 ? tmp[j - 1] : '#';
          const afterTmp = j + 6 < tmp.length ? tmp[j + 6] : '#';
          if (beforeTmp !== 'b' && afterTmp !== 'b') return true;
        }
      }
      return false;
    }

    // 사사 금수 (닫힌44도 금수임)
    isDoubleFour(pos) {
      const [x, y] = pos;
      if (!this.inBoard(x, y) || this.board[x][y] !== '-') return false;
      let total = 0;
      for (const [dx, dy] of DIRECTIONS) total += this.countFours(x, y, dx, dy);
      return total >= 2;
    }

    countFours(x, y, dx, dy) {
      const L = 5;
      let chars = this.getLinePattern(x, y, dx, dy, L); // 길이 11, 착수점은 인덱스 5
      const t = Math.floor(chars.length / 2);
      chars = chars.slice(0, t) + 'b' + chars.slice(t + 1); // 중앙에 흑돌을 놓았다고 가정
      const fours = new Set();
      for (let k = L - 4; k < L + 1; k++) { // 착수점을 포함하는 5칸 창
        const window = chars.slice(k, k + 5);
        if (count(window, 'b') !== 4 || count(window, '-') !== 1) continue; // 흑 4개 + 빈칸 1개여야 사
        const before = k - 1 >= 0 ? chars[k - 1] : '#';
        const after = k + 5 < chars.length ? chars[k + 5] : '#';
        if (before === 'b' || after === 'b') continue; // 채우면 장목이 되는 사는 제외
        const stones = [];
        for (let i = k; i < k + 5; i++) if (chars[i] === 'b') stones.push(i);
        fours.add(stones.join(',')); // 사를 이루는 돌 위치
      }
      return fours.size;
    }

    // pos 중심으로 한 방향의 문자열을 리턴하는 함수
    getLinePattern(x, y, dx, dy, length) {
      let s = '';
      for (let i = -length; i <= length; i++) {
        const nx = x + dx * i;
        const ny = y + dy * i;
        s += this.inBoard(nx, ny) ? this.board[nx][ny] : '#';
      }
      return s;
    }

    // 장목 금수
    isOverLine(pos) {
      const [x, y] = pos;
      if (!this.inBoard(x, y) || this.board[x][y] !== '-') return false;
      for (const [dx, dy] of DIRECTIONS) {
        let blackCount = 1;
        for (const sign of [-1, 1]) {
          let nx = x + sign * dx;
          let ny = y + sign * dy;
          while (this.inBoard(nx, ny) && this.board[nx][ny] === 'b') {
            blackCount++;
            nx += sign * dx;
            ny += sign * dy;
          }
        }
        if (blackCount >= 6) return true;
      }
      return false;
    }

    // 기보를 moveLog.txt 와 같은 형식의 문자열로 반환
    moveLogText() {
      return this.moveLog
        .map(([[x, y], c], i) => `${i + 1}: ((${x}, ${y}), '${c}')`)
        .join('\n') + '\n';
    }
  }

  function count(s, ch) {
    let n = 0;
    for (let i = 0; i < s.length; i++) if (s[i] === ch) n++;
    return n;
  }

  root.OmokEngine = { GameState, count };
  if (typeof module !== 'undefined') module.exports = root.OmokEngine;
})(typeof self !== 'undefined' ? self : globalThis);
