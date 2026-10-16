'''
ai algorithm v2 (Opus.5.5: 0단계 - 문제점 개선)
searching : negamax
pruning : alpha-beta pruning
evaluation(heuristic) : 돌의 패턴에 따른 점수 부여
making candidates : 미리 단순 계산으로 상위 12개 후보를 선정함. 강제수가 있다면 그 수만 탐색하도록 하여 탐색 범위를 줄임
iterative deepening : 시간 제한까지 depth = 1,2,3,... 순차적으로 탐색. 마지막 결과를 사용.

'''
from OmokEngine import GameState
import time

SCORE_TABLE = {
    (4,2): 100000,  # 열린 사
    (4,1): 10000,   # 닫힌 사
    (3,2): 1000,    # 열린 삼
    (3,1): 100,     # 닫힌 삼
    (2,2): 50,      # 열린 두
    (2,1): 10,      # 닫힌 두
}

WIN_SCORE = 1000000 # 승리점수

# 공간 점수 가중치
# 상대가 4칸 간격으로 막으면 오목을 완성할 수 없는 공간이 됨. 오목 봇이 이 위협을 인지하도록 하기 위함.
# 5목을 완성할 수 있는 공간에 있는 돌의 개수마다 이 점수를 부여함. 상대가 4칸 띄워 막으면 이 점수가 없어지므로 위협으로 인지함.
POTENTIAL_WEIGHT = 40

DIRECTIONS = [(1, 0), (0, 1), (1, 1), (1, -1)]
BOARD_SIZE = 15
MAX_CANDIDATES = 12 # 탐색할 후보수의 최대 개수
TIME_LIMIT = 2.0 # 한 수당 주어지는 탐색 시간
MAX_DEPTH = 12 # 탐색 최대 깊이

# 탐색 시간 관리용 전역 변수
class SearchTimeout(Exception): # 시간이 다 되면 즉시 탐색 종료 시키기 위한 예외
    pass
searchDeadline = float('inf') # 이 시각이 지나면 탐색 중단
nodeCount = 0                 # 탐색한 노드 수

# 보드의 모든 줄(가로, 세로, 대각선 2개)의 좌표 목록을 미리 만들어 둠
# 길이가 5 미만인 대각선은 5목이 나올 수 없으므로 제외 (게산할 필요 없음)
def makeLines(size):
    lines = []
    for dx, dy in DIRECTIONS:
        for x in range(size):
            for y in range(size):
                # 줄의 시작점: 한 칸 뒤가 보드 밖인 좌표
                if 0 <= x - dx < size and 0 <= y - dy < size:
                    continue
                line = []
                cx, cy = x, y
                while 0 <= cx < size and 0 <= cy < size:
                    line.append((cx, cy))
                    cx += dx
                    cy += dy
                if len(line) >= 5:
                    lines.append(line)
    return lines
LINES = makeLines(BOARD_SIZE)
LINE_CACHE = {} # 속도 개선용, 변화가 없는 줄은 저장해 두고 사용

# 좌표pos 가 몇번째 줄의 몇번째 칸에 위치하는지 저장함 [(줄번호, 칸번호), ...]
# 후보수 선정에서 착수점 기준으로 점수를 계산할 때 사용
POS_LINES= {}
def makePosLines():
    for idxLine, line in enumerate(LINES):
        for idxPos, pos in enumerate(line):
            POS_LINES.setdefault(pos, []).append((idxLine, idxPos))
makePosLines()

# pos 기준 패턴을 추출하는 함수, 후보수 정렬 및 후보수 축소를 위한 함수
# me  : 내가 pos 에 둔 경우 내 패턴 (전, 후)
# opp : 상대가 pos 에 둔 경우 상대 패턴 (전, 후), 내가 pos 에 둔 뒤의 상대 패턴
def analyzeMove(board, pos, color, oppColor):
    meBefore, meAfter = [0] * 8, [0] * 8
    oppBefore, oppAfter = [0] * 8, [0] * 8
    oppBlocked = [0] * 8
    for idxLine, idxPos in POS_LINES.get(pos, []):
        # 라인 문자열을 만들고 pos 에 흑돌, 백돌을 두었을 때 라인을 만듦
        chars = ''.join(board[x][y] for x, y in LINES[idxLine])
        myLine = chars[:idxPos] + color + chars[idxPos + 1:]
        oppLine = chars[:idxPos] + oppColor + chars[idxPos + 1:]
        for total, counts in ((meBefore, countLinePatterns(chars, color)),
                              (meAfter, countLinePatterns(myLine, color)),
                              (oppBefore, countLinePatterns(chars, oppColor)),
                              (oppAfter, countLinePatterns(oppLine, oppColor)),
                              (oppBlocked, countLinePatterns(myLine, oppColor))):
            for i in range(8):
                total[i] += counts[i]
    return meBefore, meAfter, oppBefore, oppAfter, oppBlocked

# 함수의 탐색수를 줄이기 위한 후보수 선정, radius 범위 이내의 좌표를 후보로 정함
def getCandidateMoves(gs, radius = 2):
    # ai가 두번째 수는 첫 수에 붙여서 두도록 제한함.
    if len(gs.moveLog) == 1:
        radius = 1
    # 후보수 선정
    candidates = []
    for x in range(len(gs.board)):
        for y in range(len(gs.board)):
            if gs.board[x][y] == '-':
                continue
            for nx in range(x - radius, x + radius + 1):
                for ny in range(y - radius, y + radius + 1):
                    if 0 <= nx < len(gs.board) and 0 <= ny < len(gs.board) and gs.board[nx][ny] == '-':
                        candidates.append((nx, ny))
    # 중복 제거
    candidates = list(set(candidates))
    # 흑차례이면 금수는 고려하지 않음 (금수 제거)
    if gs.blackToPlay:
        for i in range(len(candidates) - 1, -1, -1):
            if gs.getForbiddenMove(candidates[i]) and not gs.isWin(candidates[i]): #
                candidates.pop(i)

    # 후보개선2차 : 강제수 + 수 정렬 + 후보수 축소
    # 강제수 : 강제성이 높은 수, 다른 수를 고려할 필요가 없는 수준의 위협
    # 수정렬 + 후보수 축소 : 후보수의 점수를 간단히 측정한 뒤, 상위 MAX_CANDIDATES 개의 후보수만 탐색 (탐색범위를 줄이고, depth를 높이기 위함)
    color = 'b' if gs.blackToPlay else 'w'
    oppColor = 'w' if gs.blackToPlay else 'b'
    # 강제수 후보
    myWins = [] # 내가 오목을 만들 수 있는 수
    oppWins = []  # 상대가 오목을 만들 수 있는 수
    oppOpenFour = False # 상대가 다음수에 열린사를 만들수 있는지 여부
    scored = []

    for pos in candidates:
        meBefore, meAfter, oppBefore, oppAfter, oppBlocked = analyzeMove(gs.board, pos , color , oppColor)
        # 강제수 (오목을 완성하는 경우)
        if meAfter[0] > 0:
            myWins.append(pos)
        if oppAfter[0] > 0:
            oppWins.append(pos)
        # 강제수 (상대가 사목을 만들 수 있는 경우 (삼목), 흑의 금수는 제외)
        # Opus.5.5: 수정 'oppAfter[1] > 0' -> 'oppAfter[1] > oppBefore[1]'
        # 이 자리에 두었을 때 열린4가 "새로 생기는지"를 봐야 함 (이미 있던 열린4까지 세면 잘못된 강제수가 됨)
        if oppAfter[1] > oppBefore[1] and not (oppColor == 'b' and gs.getForbiddenMove(pos)):
            oppOpenFour = True
        # 후보수 정렬 (착수점 기준 점수 부여, 사를 만드는 수, 공격을 막는 수)
        isMakingFour = meAfter[1] + meAfter[2] > meBefore[1] + meBefore[2]
        isBlocking = oppBlocked[3] < oppBefore[3] or oppBlocked[2] < oppBefore[2] or oppBlocked[1] < oppBefore[1]
        score = (getSimpleScore(meAfter) - getSimpleScore(meBefore)) + (getSimpleScore(oppAfter) - getSimpleScore(oppBefore))
        scored.append((score, pos, isMakingFour, isBlocking))

    # 내가 이기는 수가 있으면 그 수만 탐색함
    if myWins:
        return myWins[:1]
    # 상대가 이기는 수가 있으면 막는 수만 탐색
    if oppWins:
        return oppWins
    # 상대가 열린삼이 있으면 막는 수 또는 사를 만드는 수 만 탐색
    # 보류 중 : 사를 쳐서 오히려 상대에게 도움이 되는 상황이 발생하는 지 확인해야함. 확실하지 않음
    if oppOpenFour:
        forcedMove = [m for m in scored if m[2] or m[3]]
        if forcedMove:
            scored = forcedMove

    # 점수가 높은 순서로 정렬, 상위 MAX_CANDIDATE 개만 탐색함
    scored.sort(key=lambda m: m[0], reverse=True)
    return [m[1] for m in scored[:MAX_CANDIDATES]]

# 후보수의 정렬을 위한 단순한 점수 계산
def getSimpleScore(counts):
    return (counts[0] * WIN_SCORE
            + counts[1] * SCORE_TABLE[(4,2)] + counts[2] * SCORE_TABLE[(4,1)]
            + counts[3] * SCORE_TABLE[(3,2)] + counts[4] * SCORE_TABLE[(3,1)]
            + counts[5] * SCORE_TABLE[(2,2)] + counts[6] * SCORE_TABLE[(2,1)]
            + counts[7])  # Opus.5.5: 공간 점수는 가중치 없이(1배) 사용. '+ POTENTIAL_WEIGHT' 는 오타로 보이지만, '* POTENTIAL_WEIGHT' 로 고치면 수 정렬이 공간 위주가 되어 오히려 약해짐 (원본과 8판: 2승 6패 -> 1배로 두면 3승 2패 3무)

'''
평가함수 (휴리스틱)
1. 승리하는 경우 INF
2. 열린4 : 100000
3. 닫힌4 : 10000
4. 열린3 : 1000
5. 닫힌3 : 100
6. 열린2 : 50
7. 닫힌2 : 10
'''
# 평가함수. 현재 보드의 점수를 흑 기준으로 계산
# 모든 줄을 문자열로 읽음 -> 패턴 추출 -> SCORE_TABLE 으로 점수 부여
def evaluate(gs):
    board = gs.board
    counts = {'b' : [0] * 8, 'w' : [0] * 8 } # 패턴의 개수를 저장하는 딕셔너리
    for line in LINES:
        chars = ''.join(board[x][y] for x, y in line)
        if 'b' not in chars and 'w' not in chars: # 빈 줄은 건너뛰기
            continue
        for color in ('b', 'w'):
            if color not in chars:
                continue
            count = countLinePatterns(chars, color)
            total = counts[color]
            for i in range(8):
                total[i] += count[i]
    return scoreFromCounts(counts['b'], True) - scoreFromCounts(counts['w'], False)

# 패턴 개수를 점수로 변환하는 함수
# counts : [5목, 열린4, 닫힌4, 열린3, 닫힌3, 열린2, 닫힌2, 공간점수]
def scoreFromCounts(counts, isBlack):
    five, open4, closed4, open3, closed3, open2, closed2, potential = counts
    if five > 0: # 승리
        return WIN_SCORE
    # 점수 계산
    score = (open4 * SCORE_TABLE[(4,2)] + closed4 * SCORE_TABLE[(4,1)]
             + open3 * SCORE_TABLE[(3,2)] + closed3 * SCORE_TABLE[(3,1)]
             + open2 * SCORE_TABLE[(2,2)] + closed2 * SCORE_TABLE[(2,1)]
             + potential * POTENTIAL_WEIGHT)
    # 강한 공격 (4,3 이나 4,4 처럼 막을 수 없는 수)
    # Opus.5.5: 버그 수정 open4 -> closed4. 열린4는 이미 막을 수 없는 수라서 4-3 판정은 닫힌4 + 열린3 이어야 함
    # (기존 코드는 열린4가 있을 때만 보너스를 줘서, 정작 닫힌4 + 열린3 (4-3) 을 알아보지 못했음)
    if closed4 >= 1 and open3 >= 1: # 4,3 은 열린4 점수를 부여함
        score += SCORE_TABLE[(4,2)]
    if closed4 >= 2 and isBlack == False: # 백의 4,4 는 열린4 점수를 부여함
        score += SCORE_TABLE[(4,2)]
    return score


'''
한 라인에서 패턴의 개수를 세는 함수, 결과는 LINE_CACHE 에 저장함
내 돌 = 'x', 빈 칸 = '-', 상대 돌과 벽 = '#'
line = 문자열, color = 기준 색
window 매칭 아이디어
'''
def countLinePatterns(line, color):
    key = (line, color)
    if key in LINE_CACHE:
        return LINE_CACHE[key]

    isBlack = color == 'b'
    chars = '#' + ''.join('x' if ch == color else ('-' if ch == '-' else '#') for ch in line) + '#'
    n = len(chars)

    # 5칸 윈도우 안에 돌 k개 + 나머지 빈칸 -> 돌 위치를 묶음 (중복 카운트 방지)
    def stoneSets(k):
        result = set()
        for i in range(1, n-5):
            window = chars[i:i+5]
            if '#' in window or window.count('x') != k: # 보드 바깥 or 돌 개수 != k 인 경우
                continue
            if isBlack and (chars[i-1] == 'x' or chars[i+5] == 'x'): # 흑의 장목 처리
                continue
            result.add(tuple(j for j in range(i,i+5) if chars[j]=='x'))
        return result

    # 열린 4 '-xxxx-' 위치 반환 함수
    def openFourStones(t):
        result = set()
        start = t.find('-xxxx-')
        while start != -1:
            before = t[start-1] if start - 1 >= 0 else '#'
            after = t[start+6] if start + 6 < len(t) else '#'
            if not (isBlack and (before == 'x' or after == 'x')):
                result.add(tuple(range(start+1, start+5)))
            start = t.find('-xxxx-', start + 1)
        return result

    # 5목
    five = 0
    for i in range(1, n - 4):
        if chars[i:i+5] == 'xxxxx':
            if isBlack and (chars[i-1] == 'x' or chars[i+5] == 'x'): # 흑의 장목 처리
                continue
            five = 1
            break

    # 4목
    fours = stoneSets(4)
    open4 = openFourStones(chars)

    # 3목
    # 열린 삼 (돌을 하나 더 두었을 때 열린 4가 되는 3개의 돌)
    open3 = set()
    if chars.count('x') >= 3:
        for i in range(1, n-1):
            if chars[i] != '-':
                continue
            tmp = chars[:i] + 'x' + chars[i+1:] # 좌표 i 에 돌을 하나 둬 봄
            for stones in openFourStones(tmp): # 돌을 두었을 때 열린 4가 된다면, 열린 삼
                if i in stones:
                    open3.add(tuple(j for j in stones if j != i)) # 열린 삼 좌표는 열린 사 에서 i 돌을 뺀 것
    threes = stoneSets(3)

    # 2목
    # 열린 2 (6칸 윈도우에서 양 끝이 빈칸이고, 중앙에 돌2개 빈칸 2개인 경우)
    twos = stoneSets(2)
    open2 = set()
    for i in range(0, n - 5):
        window = chars[i:i+6]
        if window[0] != '-' or window[5] != '-' or '#' in window or window.count('x') != 2:
            continue
        open2.add(tuple(j for j in range(i, i+6) if chars[j] == 'x'))
    open2 &= twos

    # 큰 패턴의 일부인 작은 패턴은 중복으로, 세지 않음
    # 큰 패턴에 포함되지 않는 작은 패턴들만 반환함
    def notInside(small, bigs):
        return {a for a in small if not any(set(a) <= set(b) for b in bigs)}

    bigFours = fours | open4
    open3 = notInside(open3, bigFours)
    threes = notInside(threes, bigFours)
    bigThrees = bigFours | threes | open3
    twos = notInside(twos, bigThrees)
    open2 = notInside(open2, bigThrees)

    # 공간점수
    potential = 0
    for i in range(1, n-5):
        window = chars[i:i+5]
        if '#' in window:
            continue
        if isBlack and (chars[i-1] == 'x' or chars[i+5] == 'x'): # 흑 장목
            continue
        potential += window.count('x')

    result = (five,
              len(open4), len(fours-open4),
              len(open3), len(threes-open3),
              len(open2), len(twos-open2),
              potential)
    LINE_CACHE[key] = result
    return result

'''
Opus.5.5: 설명 수정 (minimax 설명이 남아 있었음)
negamax : 점수를 항상 "지금 둘 차례인 쪽" 기준으로 계산함 (양수 = 차례인 쪽이 유리)
자식 노드의 점수는 상대 기준이므로 부호를 뒤집어서 사용 -> 모든 노드에서 최댓값만 고름

depth : 남은 탐색 깊이
alpha : 지금 차례인 쪽이 이미 확보한 최선의 점수 (하한)
beta  : 상대가 허용하는 최대 점수 (상한). alpha >= beta 이면 상대는 이 수순을 피하므로 더 볼 필요 없음
자식에게 넘길 때는 기준이 상대로 바뀌므로 창을 (-beta, -alpha) 로 뒤집어서 넘김
'''
def negamax(gs, depth, alpha, beta):
    # 32 노드 마다 시간 확인
    global nodeCount
    nodeCount += 1
    if nodeCount % 32 == 0 and time.time() > searchDeadline:
        raise SearchTimeout

    # 승부가 난 노드 = 직전에 상대가 5목을 만든 상태 -> 지금 차례인 쪽은 항상 진 것
    # depth 가 많이 남아 있을수록(= 더 빨리 졌을수록) 더 나쁜 점수 -> 빠른 승리 / 늦은 패배를 선호
    if gs.blackWin or gs.whiteWin:
        return -(WIN_SCORE + depth), None

    # 평가함수는 흑 기준이므로 백 차례이면 부호를 뒤집음
    if depth == 0:
        score = evaluate(gs)
        return (score if gs.blackToPlay else -score), None

    candidates = getCandidateMoves(gs)
    if not candidates:
        score = evaluate(gs)
        return (score if gs.blackToPlay else -score), None

    bestScore = -float('inf')
    bestPos = ()
    for move in candidates:
        # 착수에 실패하면(금수 등) undoMove 가 직전 수를 지우지 않도록 건너뜀
        if not gs.placeStone(move):
            continue
        # 탐색 도중 시간초과 시 이미 착수한 돌은 반드시 (undo)되돌려야함
        try:
            score, _ = negamax(gs, depth - 1, -beta, -alpha)
        finally:
            gs.undoMove()
        score = -score  # 상대 기준 점수 -> 내 기준 점수
        # 같은 점수면 먼저 본 수를 유지 (가지치기로 잘린 수는 점수가 경계값이므로)
        if not bestPos or score > bestScore:
            bestScore = score
            bestPos = move
        alpha = max(alpha, score)
        if alpha >= beta:
            break
    return bestScore, bestPos

# 루트탐색
# 이전 탐색의 최선 수 먼저 탐색
def searchRoot(gs, depth, candidates, firstMove):
    # 이전 탐색의 최선 수를 후보수의 가장 앞에 배치함
    if firstMove in candidates:
        candidates = [firstMove] + [m for m in candidates if m != firstMove]
    alpha, beta = -float('inf'), float('inf')
    bestScore = -float('inf')
    bestPos = ()
    for move in candidates:
        if not gs.placeStone(move):
            continue
        try:
            score, _ = negamax(gs, depth - 1, -beta, -alpha)
        finally:
            gs.undoMove()
        score = -score
        if not bestPos or score > bestScore:
            bestScore = score
            bestPos = move
        alpha = max(alpha, score)
    return bestScore, bestPos

# ai는 백돌을 둔다
def aiMove(gs):
    # 첫 수는 중앙
    if len(gs.moveLog) == 0:
        return 7, 7

    # iterative deepening
    global nodeCount, searchDeadline
    nodeCount = 0
    startTime = time.time()
    candidates = getCandidateMoves(gs)

    if not candidates:
        return ()
    if len(candidates) == 1: # 강제수가 하나이면 탐색하지 않아도 됨
        print("AI 착수:", candidates[0], "(강제수)")
        return candidates[0]

    bestScore, bestPos, reachedDepth = 0, candidates[0], 0
    for depth in range(1, MAX_DEPTH + 1):
        searchDeadline = float('inf') if depth == 1 else startTime + TIME_LIMIT # 시작시각+제한시간
        try:
            score, pos = searchRoot(gs, depth, candidates, bestPos)
        except SearchTimeout: # 탐색 중간에 타임아웃 시 결과를 버림
            break
        if pos:
            bestScore, bestPos, reachedDepth = score, pos, depth
        # 이기거나 지는 수순 발견 시 더 이상 탐색하지 않음
        if abs(bestScore) >= WIN_SCORE:
            break
        # 다음 탐색을 시간 내에 못 끝낼 가능성이 매우 높으므로 탐색을 미리 중단함
        if time.time() - startTime > TIME_LIMIT / 2:
            break

    blackScore = bestScore if gs.blackToPlay else -bestScore
    print("AI 착수:", bestPos, "평가 점수:", blackScore,
          "깊이:", reachedDepth, "노드:", nodeCount, "시간: %.2f초" % (time.time() - startTime))  # 디버그용 출력
    return bestPos
