'''
this class is responsible for storing all the information about current state of a game
'''

class GameState():
    def __init__(self):
        self.board = [
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ['-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-', '-'],
            ]
        self.blackToPlay = True
        self.whiteWin = False
        self.blackWin = False
        self.moveLog = []

    def placeStone(self, pos):
        x = pos[0]
        y = pos[1]
        if not (0 <= x < len(self.board) and 0 <= y < len(self.board[x])):
            return False
        if self.board[x][y] != '-':
            return False

        # 승리 판정
        if self.isWin(pos):
            # 승리
            winner = "black" if self.blackToPlay else "white"
            if winner == "black":
                self.blackWin = True
            else:
                self.whiteWin = True
            self.board[x][y] = 'b' if self.blackToPlay else 'w'
            # ai 를 위한 로그 추가, 턴 바꾸기
            self.moveLog.append((pos, self.board[x][y]))
            self.blackToPlay = not self.blackToPlay
            return True

        # 흑 차례이면 금수 판정 함수를 호출, 금수인 경우 착수 금지
        if self.blackToPlay and self.getForbiddenMove(pos):
            return False

        # 착수, 턴 교대
        self.board[x][y] = 'b' if self.blackToPlay else 'w'
        self.blackToPlay = not self.blackToPlay
        self.moveLog.append((pos, self.board[x][y]))
        return True

    def undoMove(self):
        if len(self.moveLog) == 0:
            return
        pos, color = self.moveLog.pop()
        self.board[pos[0]][pos[1]] = '-'
        self.blackToPlay = not self.blackToPlay
        self.blackWin = False
        self.whiteWin = False
        return

    def isWin(self, pos):
        x = pos[0]
        y = pos[1]
        directions = [(1, 0), (0, 1), (1, 1), (1, -1)]
        currentPlayer = 'b' if self.blackToPlay else 'w'
        if not (0 <= x < len(self.board) and 0 <= y < len(self.board[x])):
            return False
        if self.board[x][y] != '-':
            return False
        for dx, dy in directions:
            stoneCount = 1
            for sign in [-1, 1]: # 양 방향으로 탐색함
                nx = x + sign * dx
                ny = y + sign * dy
                while 0 <= nx < len(self.board) and 0 <= ny < len(self.board[nx]) and self.board[nx][ny] == currentPlayer:
                    stoneCount += 1
                    nx += sign * dx
                    ny += sign * dy
            if currentPlayer == 'b' and stoneCount == 5: # 흑은 정확히 5개의 돌인 경우 승리
                return True
            elif currentPlayer == 'w' and stoneCount >= 5: # 백은 6목 이상도 허용
                return True
        return False

    # 금수 판정, 흑돌의 경우 33, 44, 장목이 금지됨
    def getForbiddenMove(self, pos):
        return self.isDoubleThree(pos) or self.isDoubleFour(pos) or self.isOverLine(pos)

    # 삼삼 금수
    def isDoubleThree(self, pos):
        x, y = pos
        directions = [(1, 0), (0, 1), (1, 1), (1, -1)]
        doubleThreePossible = False
        if not(0 <= x < len(self.board) and 0 <= y < len(self.board[x])):
            return False
        if self.board[x][y] != '-':
            return False

        for dx, dy in directions:
            if self.isOpenThree(x, y, dx, dy):
                if doubleThreePossible == False:
                    doubleThreePossible = True
                else:
                    return True
        return False

    # 열린 삼 판정, 흑돌 하나를 두었을 때 열린 사가 되면 열린 삼
    def isOpenThree(self, x, y, dx, dy):
        # 길이 13
        chars = self.getLinePattern(x, y, dx, dy, 6)
        c = len(chars)//2
        chars = chars[:c] + 'b' + chars[c+1:] # 중앙에 흑돌을 두었다고 가정
        for i in range(len(chars)):
            if chars[i] != '-':
                continue
            tmp = chars[:i] + 'b' + chars[i+1:] # 빈칸에 흑돌을 하나 두어 봄
            for j in range(len(chars) - 5):
                # "열린 사"이면서, 착수점이 포함인 경우 열린 삼 판정
                if tmp[j:j+6] != "-bbbb-": # 연결된 사 확인
                    continue
                if not (j < len(chars)//2 < j+6): # 착수점이 포함되는지 확인
                    continue
                # 열린 사가 아닌 경우 확인 (장목이 되는 경우)
                before_tmp = tmp[j-1] if j-1 >= 0 else '#'
                after_tmp = tmp[j+6] if j+6 < len(tmp) else '#'
                if before_tmp != 'b' and after_tmp != 'b':
                    return True
        return False

    # 사사 금수 (닫힌44도 금수임)
    def isDoubleFour(self, pos):
        x, y = pos
        if not (0 <= x < len(self.board) and 0 <= y < len(self.board)) or self.board[x][y] != '-':
            return False
        total = 0
        for dx, dy in [(1, 0), (0, 1), (1, 1), (1, -1)]:
            total += self.countFours(x, y, dx, dy)
        return total >= 2

    #
    def countFours(self, x, y, dx, dy):
        L = 5
        chars = self.getLinePattern(x, y, dx, dy, L)  # 길이 11, 착수점은 인덱스 5
        t = len(chars)//2
        chars = chars[:t] + 'b' + chars[t+1:] # 중앙에 흑돌을 놓았다고 가정
        c = L
        fours = set()
        for k in range(c - 4, c + 1):  # 착수점을 포함하는 5칸 창
            window = chars[k:k + 5]
            if window.count('b') != 4 or window.count('-') != 1:
                continue  # 흑 4개 + 빈칸 1개여야 사
            before = chars[k - 1] if k - 1 >= 0 else '#'
            after = chars[k + 5] if k + 5 < len(chars) else '#'
            if before == 'b' or after == 'b':  # 채우면 장목이 되는 사는 제외
                continue
            fours.add(tuple(i for i in range(k, k + 5) if chars[i] == 'b'))  # 사를 이루는 돌 위치
        return len(fours)

    # pos 중심으로 한 뱡향의 문자열을 리턴하는 함수
    def getLinePattern(self, x, y, dx, dy, length):
        chars = []
        for i in range(-length, length+1):
            nx = x + dx * i
            ny = y + dy * i
            if 0 <= nx < len(self.board) and 0 <= ny < len(self.board[x]):
                chars.append(self.board[nx][ny])
            else:
                chars.append('#')
        return ''.join(chars)

    # 장목 금수
    def isOverLine(self, pos):
        x = pos[0]
        y = pos[1]
        directions = [(1, 0), (0, 1), (1, 1), (1, -1)]
        if not (0 <= x < len(self.board) and 0 <= y < len(self.board[x])):
            return False
        if self.board[x][y] != '-':
            return False
        for dx, dy in directions:
            blackCount = 1
            for sign in [-1, 1]: # 양 방향으로 탐색함
                nx = x + sign * dx
                ny = y + sign * dy
                while 0 <= nx < len(self.board) and 0 <= ny < len(self.board[nx]) and self.board[nx][ny] == 'b':
                    blackCount += 1
                    nx += sign * dx
                    ny += sign * dy
            if blackCount >= 6:
                return True
        return False

    def saveMoveLog(self, filename="moveLog.txt"):
        with open(filename, "w", encoding="utf-8") as f:
            for i, move in enumerate(self.moveLog, start=1):
                f.write(f"{i}: {move}\n")