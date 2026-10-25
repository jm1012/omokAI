'''
ai algorithm v3 + (반복 심화 + Zobrist hash + 증분평가)
searching : negamax
pruning : alpha-beta pruning
evaluation(heuristic) : 돌의 패턴에 따른 점수 부여
making candidates : 미리 단순 계산으로 상위 12개 후보를 선정함. 강제수가 있다면 그 수만 탐색하도록 하여 탐색 범위를 줄임
iterative deepening : 시간 제한까지 depth = 1,2,3,... 순차적으로 탐색. 마지막 결과를 사용.
zobrist hash : 앞서 탐색한 국면의 해시를 저장하고 같은 국면이 나오면 그 값을 사용함.
incremental evaluation : 착수점을 포함하는 4 방향의 선만 계산하여 평가점수를 갱신함.
VCF : 사를 연속으로 두어 이기는 수순 찾기. 나의 VCF 가 있으면 바로 두고 상대의 VCF 가 있으면 막는 수만 탐색
리프 VCF : 탐색의 끝 노드 (depth=0) 에서 차례인 쪽의 짧은 VCF 확인해서 수평선효과를 줄임. (의미없는 시간끌기용 사)
'''
from OmokEngine import GameState
import time # 반복 심화 시간제한
import random # Zobrist 해시

SCORE_TABLE = {
    (4,2): 100000,  # 열린 사
    (4,1): 10000,   # 닫힌 사
    (3,2): 1000,    # 열린 삼
    (3,1): 100,     # 닫힌 삼
    (2,2): 50,      # 열린 두
    (2,1): 10,      # 닫힌 두
}

WIN_SCORE = 1000000 # 승리점수
WIN_THRESHOLD = WIN_SCORE - 1000 # 리프 VCF 에서 사용할 승리점수. (승리점수 - VCF 수순 길이)가 이 값보다 크면 승리 수순으로 간주

# 공간 점수 가중치
# 상대가 4칸 간격으로 막으면 오목을 완성할 수 없는 공간이 됨. 오목 봇이 이 위협을 인지하도록 하기 위함.
# 5목을 완성할 수 있는 공간에 있는 돌의 개수마다 이 점수를 부여함. 상대가 4칸 띄워 막으면 이 점수가 없어지므로 위협으로 인지함.
POTENTIAL_WEIGHT = 40

DIRECTIONS = [(1, 0), (0, 1), (1, 1), (1, -1)]
BOARD_SIZE = 15
MAX_CANDIDATES = 12 # 탐색할 후보수의 최대 개수
TIME_LIMIT = 2.0 # 한 수당 주어지는 탐색 시간
MAX_DEPTH = 12 # 탐색 최대 깊이
THREAT_TIME_RATIO = 0.3 # VCT 탐색에 사용할 시간 비율

# 탐색 시간 관리용 전역 변수
class SearchTimeout(Exception): # 시간이 다 되면 즉시 탐색 종료 시키기 위한 예외
    pass
searchDeadline = float('inf') # 이 시각이 지나면 탐색 중단
nodeCount = 0                 # 탐색한 노드 수

'''
Zobrist hash
(칸, 색깔) 마다 64bit 랜덤 숫자를 부여 15x15x2 = 450 가지
국면의 해시 = 놓인 돌의 숫자를 전부 xor 한 값, 백 차례이면 Zobrist_side 도 xor
돌을 놓을 때 그 숫자만 xor 하면 됨. 무를 때도 동일
착수 순서에 관련 없이 같은 배치면 같은 해시
'''
_rng = random.Random(20261012) # 디버깅 쉽게 하기 위해 시드 고정
ZOBRIST = {(x,y):{'b':_rng.getrandbits(64), 'w':_rng.getrandbits(64) }
           for x in range(BOARD_SIZE)
           for y in range(BOARD_SIZE)}
ZOBRIST_SIDE = _rng.getrandbits(64) # 차례정보

# 현재 보드의 해시를 처음부터 계산
def computeHash(gs):
    h = 0
    for x in range(BOARD_SIZE):
        for y in range(BOARD_SIZE):
            if gs.board[x][y] in ('b', 'w'):
                h ^= ZOBRIST[(x,y)][gs.board[x][y]]
    if not gs.blackToPlay:
        h ^= ZOBRIST_SIDE
    return h

# 돌을 하나 둔 다음 해시 계산
def nextHash(h, pos, color):
    return h ^ ZOBRIST[(pos[0], pos[1])][color] ^ ZOBRIST_SIDE

'''
전치표 (transposition table)
TT[해시] = (탐색깊이, 점수, 점수종류, 최선수)
점수 종류 : alpha-beta 로 잘린 노드의 점수는 정확한 값이 아니라 정확히 구분
EXACT : 정확한 값 (alpha < 점수 < beta)
LOWER : 하한, 실제 점수 >= 저장된 점수 (beta 이상이라 잘림)
UPPER : 상한, 실제 점수 <= 저장된 점수 (alpha를 넘는 수가 없음)
CANDIDATE_CACHE[해시] = 후보수 목록 : 후보수 선정은 오직 국면에 의해 결정됨, 같은 국면이면 계산할 필요 없음
(반복 심화에서 큰 효과를 기대할 수 있음)
'''
EXACT, LOWER, UPPER = 0, 1, 2
TT = {}
CANDIDATE_CACHE = {}
TT_MAX_SIZE = 500000 # 표가 커지면 메모리가 커지므로 이 값을 초과하면 표를 비움
ttHits = 0 # (디버그용) hit 횟수

def getCandidatesCached(gs, h):
    cands = CANDIDATE_CACHE.get(h)
    if cands is None:
        cands = getCandidateMoves(gs)
        CANDIDATE_CACHE[h] = cands
    return cands

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
    for idxLine, idxPos in POS_LINES.get(pos, []): # pos 키가 없으면 빈 리스트를 반환
        # 라인 문자열을 만들고 pos 에 흑돌, 백돌을 두었을 때 라인을 만듦
        # 증분상태가 있다면 저장된 문자열을 그대로 사용
        chars = incLineStrs[idxLine] if incActive else ''.join(board[x][y] for x, y in LINES[idxLine])
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
            + counts[7])  # 공간 점수는 가중치 없이(1배) 사용.

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

'''
증분평가
돌을 둘 때 착수점을 포함한 4방향의 줄만 변화하므로 해당 줄만 계산함.
다른 줄의 정보는 저장해 둠
incLineStrs[줄 번호]   : 그 줄의 현재 문자열
incLineCounts[줄 번호] : 그 줄의 현재 패턴 개수
incTotals             : 모든 줄의 패턴 개수 합계 (평가점수 계산용)
incStack              : 착수하기 전 값을 저장 (무를때 필요)
탐색중 makeMove / unmakeMove 를 함께 사용해야 점수가 정상 유지됨
INC_DEBUG = True 이면 증분평가와 evaluate 를 함께 실행해서 값을 비교함 (디버그용)
'''
INC_DEBUG = False
incActive = False
incLineStrs = []
incLineCounts = []
incTotals = {'b': [0]*8, 'w': [0]*8 }
incStack = []

# 현재 보드에서 증분상태를 새로 계산 (aiMove 실행시 한번 실행)
def incInit(gs):
    global incActive, incLineStrs, incLineCounts, incTotals, incStack
    incLineStrs = [''.join(gs.board[x][y] for x,y in line) for line in LINES]
    incLineCounts = []
    incTotals = {'b': [0]*8, 'w': [0]*8 }
    for chars in incLineStrs:
        counts = {color: countLinePatterns(chars, color) for color in ('b', 'w')}
        incLineCounts.append(counts)
        for i in range(8):
            incTotals['b'][i] += counts['b'][i]
            incTotals['w'][i] += counts['w'][i]
    incStack = []
    incActive = True

# pos 에 color 돌을 두었을 때 지나는 줄만 갱신
def incPlace(pos, color):
    saved = []
    for idxLine, idxPos in POS_LINES.get(pos, []):
        # 착수 이전 문자열과 패턴 개수
        strBefore = incLineStrs[idxLine]
        cntBefore = incLineCounts[idxLine]
        # 착수 이후 문자열과 패턴 개수
        strAfter = strBefore[:idxPos] + color + strBefore[idxPos+1:]
        cntAfter = {c:countLinePatterns(strAfter, c) for c in ('b', 'w')}
        # 전체 패턴 개수를 갱신
        for c in ('b', 'w'):
            total, before, after = incTotals[c], cntBefore[c], cntAfter[c] # 딕셔너리를 매번 찾기 않기 위함 (매우 작은 차이)
            for i in range(8):
                total[i] += -before[i] + after[i]
        # 업데이트
        incLineStrs[idxLine] = strAfter
        incLineCounts[idxLine] = cntAfter
        saved.append((idxLine, strBefore, cntBefore)) # 착수전 정보
    incStack.append(saved)

# 마지막으로 둔 돌을 되돌림
def incUndo():
    for idxLine, strBefore, cntBefore in incStack.pop():
        strAfter = incLineStrs[idxLine]
        cntAfter = incLineCounts[idxLine]
        incLineStrs[idxLine] = strBefore
        incLineCounts[idxLine] = cntBefore
        for c in ('b', 'w'):
            total, before, after = incTotals[c], cntBefore[c], cntAfter[c]
            for i in range(8):
                total[i] += before[i] - after[i]

# 탐색용 착수 / 무르기 : 보드와 증분 상태를 함께 바꿈
def makeMove(gs, move):
    color = 'b' if gs.blackToPlay else 'w'
    if not gs.placeStone(move): # 착수 불가능
        return False
    if incActive:
        incPlace(move, color)
    return True

def unmakeMove(gs):
    gs.undoMove()
    if incActive:
        incUndo()

# 증분 상태로 점수 계산
def evaluateInc(gs):
    if not incActive:
        return evaluate(gs)
    score = scoreFromCounts(incTotals['b'], True) - scoreFromCounts(incTotals['w'], False)
    if INC_DEBUG:
        full = evaluate(gs)
        assert score == full, ("증분 평가 불일치", score, full)
    return score

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
    # 버그 수정 open4 -> closed4. 열린4는 이미 막을 수 없는 수라서 4-3 판정은 닫힌4 + 열린3 이어야 함
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
negamax : 점수를 항상 "지금 둘 차례인 쪽" 기준으로 계산함 (양수 = 차례인 쪽이 유리)
자식 노드의 점수는 상대 기준이므로 부호를 뒤집어서 사용 -> 모든 노드에서 최댓값만 고름

depth : 남은 탐색 깊이
alpha : 지금 차례인 쪽이 이미 확보한 최선의 점수 (하한)
beta  : 상대가 허용하는 최대 점수 (상한). alpha >= beta 이면 상대는 이 수순을 피하므로 더 볼 필요 없음
자식에게 넘길 때는 기준이 상대로 바뀌므로 창을 (-beta, -alpha) 로 뒤집어서 넘김
hash : 해시값, None 이면 새로 계산함
'''
def negamax(gs, depth, alpha, beta, hash = None):
    # 32 노드 마다 시간 확인
    global nodeCount
    nodeCount += 1
    if nodeCount % 32 == 0 and time.time() > searchDeadline:
        raise SearchTimeout

    # 승부가 난 노드 = 직전에 상대가 5목을 만든 상태 -> 지금 차례인 쪽은 항상 진 것
    # depth 가 많이 남아 있을수록(= 더 빨리 졌을수록) 더 나쁜 점수 -> 빠른 승리 / 늦은 패배를 선호
    if gs.blackWin or gs.whiteWin:
        return -(WIN_SCORE + depth), None

    # 전치표 확인
    global ttHits
    if hash is None: # 새로 계산
        hash = computeHash(gs)
    alphaOrig = alpha
    ttMove = None
    entry = TT.get(hash) # 깊이, 점수, 타입, 최선수
    if entry is not None:
        eDepth, eScore, eFlag, eMove = entry
        ttMove = eMove # (깊이가 부족해서 점수를 사용하지 못해도) 최선수는 먼저 탐색할 수로 사용
        if eDepth >= depth: # 해시의 탐색 깊이가 현재 깊이보다 깊은 경우에만 해시를 사용
            if eFlag == EXACT: # 정확한 값
                ttHits += 1
                return eScore, eMove
            if eFlag == LOWER: # 하한, update alpha
                alpha = max(alpha, eScore)
            else: # 상한, update beta
                beta = min(beta, eScore)
            if alpha >= beta: # 저장된 경계값만으로 잘라내기 가능
                ttHits += 1
                return eScore, eMove

    # 평가함수는 흑 기준이므로 백 차례이면 부호를 뒤집음
    if depth == 0:
        # 리프 VCF. 사로 시간을 끌어서 승리수순을 탐색범위 밖으로 밀어내는 경우를 없에기 위함
        if leafHasFourChance(gs):
            seq = findVCF(gs, hash, VCF_LEAF_DEPTH, VCF_LEAF_LIMIT)
            if seq:
                return WIN_SCORE - len(seq), None
        # 기존 평가함수
        score = evaluateInc(gs) # v2_3_incremental : evaluate -> evaluateInc (전체 대신 증분 계산)
        return (score if gs.blackToPlay else -score), None

    candidates = getCandidatesCached(gs, hash) # 같은 국면이면 후보수를 다시 계산하지 않음
    if not candidates:
        score = evaluateInc(gs) # v2_3_incremental : evaluate -> evaluateInc
        return (score if gs.blackToPlay else -score), None

    # 전치표에 저장된 최선수를 가장 먼저 탐색함 (가지치기 강화)
    if ttMove in candidates and candidates[0] != ttMove:
        candidates = [ttMove] + [m for m in candidates if m != ttMove]

    color = 'b' if gs.blackToPlay else 'w' # hash 갱신용
    bestScore = -float('inf')
    bestPos = ()
    for move in candidates:
        # 착수에 실패하면(금수 등) undoMove 가 직전 수를 지우지 않도록 건너뜀
        if not makeMove(gs, move): # v2_3_incremental : placeStone -> makeMove
            continue
        # 탐색 도중 시간초과 시 이미 착수한 돌은 반드시 (undo)되돌려야함
        try:
            score, _ = negamax(gs, depth - 1, -beta, -alpha, nextHash(hash, move, color))
        finally:
            unmakeMove(gs) # v2_3_incremental : undoMove -> unmakeMove
        score = -score  # 상대 기준 점수 -> 내 기준 점수
        # 같은 점수면 먼저 본 수를 유지 (가지치기로 잘린 수는 점수가 경계값이므로)
        if not bestPos or score > bestScore:
            bestScore = score
            bestPos = move
        alpha = max(alpha, score)
        if alpha >= beta:
            break

    # 결과를 전치표에 저장
    if bestPos:
        if bestScore <= alphaOrig: # alpha 보다 큰 수가 없었음, 실제 점수는 이것 이하
            flag = UPPER
        elif bestScore >= beta: # beta 이상이라 잘림, 실제 점수는 이것 이상
            flag = LOWER
        else:
            flag = EXACT
        TT[hash] = (depth, bestScore, flag, bestPos)

    return bestScore, bestPos

'''
VCF (Victory by Continuous Fours)
사를 계속 두어 이기는 수순을 찾는다. 사를 두면 막는 수가 정해져 있기 때문에 더 깊은 탐색을 할 수 있음
승리 조건
1. 사를 두었을 때 오목자리가 2개 이상 (상대가 막을 수 없음)
2. 백의 VCF 에서 막아야할 자리가 금수
3. 상대의 막는 수 다음에도 VCF 가 이어짐
상대가 이미 사를 가지고 있으면 그 곳을 막아야하고, 막는 수가 사가 아니면 VCF 가 끊긴다.
'''
VCF_DEPTH = 8           # 공격측이 둘 수 있는 사의 최대 개수
VCF_NODE_LIMIT = 3000   # 한번에 볼 최대 노드 수
VCF_FAIL = {}           # VCF_FAIL[해시] = 실패가 확인 된 깊이
FIVE_IDX_CACHE = {}     # (줄 문자열, 색) -> 오목자리 인덱스
FOUR_IDX_CACHE = {}     # (줄 문자열, 색) -> 사를 만드는 자리 인덱스
vcfNodes = 0

# VCF / VCT 노드 수 초과시 중단 예외
class ThreatBudget(Exception):
    pass

# 줄 문자열
def getLineStr(board, idxLine):
    if incActive:
        return incLineStrs[idxLine]
    return ''.join(board[x][y] for x, y in LINES[idxLine])

# 줄 문자열 s에서 color 가 두었을 때 오목이 되는 빈칸의 인덱스
def fiveIndices(s, color):
    key = (s, color)
    r = FIVE_IDX_CACHE.get(key)
    if r is None:
        r = ()
        if s.count(color) >= 4:
            r = tuple(i for i in range(len(s)) if s[i] == '-' and countLinePatterns(s[:i] + color + s[i+1:], color)[0] > 0)
        FIVE_IDX_CACHE[key] = r
    return r

# 줄 문자열 s에서 color 가 두었을 때 사가 되는 빈칸의 인덱스
def fourIndices(s, color):
    key = (s, color)
    r = FOUR_IDX_CACHE.get(key)
    if r is None:
        r = ()
        if s.count(color) >= 3:
            r = tuple(i for i in range(len(s)) if s[i] == '-' and fiveIndices(s[:i] + color + s[i+1:], color))
        FOUR_IDX_CACHE[key] = r
    return r

# 보드 전체에서 color 의 오목자리
def findFives(board, color):
    result = set()
    for idxLine, line in enumerate(LINES):
        for i in fiveIndices(getLineStr(board, idxLine), color):
            result.add(line[i])
    return result

# 보드 전체에서 color 의 사목자리
def findFourMoves(board, color):
    result = set()
    for idxLine, line in enumerate(LINES):
        for i in fourIndices(getLineStr(board, idxLine), color):
            result.add(line[i])
    return sorted(result)

# pos 를 지나는 줄에서 color 의 오목 자리 (방금 둔 돌로 생긴 사, 보드에서 직접 계산)
def fivesThrough(board, pos, color):
    result = set()
    for idxLine, idxPos in POS_LINES.get(pos, []):
        line = LINES[idxLine]
        s = ''.join(board[x][y] for x, y in line)
        for i in fiveIndices(s, color):
            result.add(line[i])
    return result

# 위치 m 에 사를 두었을 때 상대가 막는 과정
# 결과 'win' : 상대가 막을 수 없음, None (사 아님 / 착수불가), (막는자리) (상대가 막아야함)
def playFour(gs, move, color):
    if not makeMove(gs, move): # 금수
        return None
    fives = fivesThrough(gs.board, move, color) # 방금 둔 자리에서 생긴 사
    if not fives:
        unmakeMove(gs)
        return None
    if len(fives) >= 2: # 열린 사, 사-사, 막을 수 없음
        unmakeMove(gs)
        return 'win'
    return min(fives) # 착수한 상태로 리턴, 호출한 함수에서 unmakeMove

# 노드 초과 또는 시간 초과 제어
def countTreatNode():
    global vcfNodes
    vcfNodes += 1
    if vcfNodes > VCF_NODE_LIMIT or (vcfNodes % 64 == 0 and time.time() > searchDeadline): # 노드 초과 또는 시간 초과
        raise ThreatBudget

# 지금 차례의 vcf 를 탐색
def vcf(gs, depth, hash):
    countTreatNode()
    me = 'b' if gs.blackToPlay else 'w'
    opp = 'w' if gs.blackToPlay else 'b'
    # 내가 이기는 수가 있으면 그 수를 둠
    myFives = findFives(gs.board, me)
    if myFives:
        return [min(myFives)]
    # 이 국면에서 VCF 가 없음을 이미 확인한 경우 (해시)
    if depth <= 0 or VCF_FAIL.get(hash, -1) >= depth:
        return None
    # 상대 오목자리가 2개 이상이면 이길 수 없음 (탐색x)
    oppFives = findFives(gs.board, opp)
    if len(oppFives) >= 2:
        return None
    # 상대가 이기는 수가 있으면 막는 경우를 탐색, 아니면 VCF 탐색을 시작함
    moves = list(oppFives) if oppFives else findFourMoves(gs.board, me)
    for m in moves:
        # m 위치에 착수 -> 상대 착수(강제수) -> 평가
        r = playFour(gs, m, me)
        if r is None:
            continue
        if r == "win":
            return [m]
        block = r
        hash1 = nextHash(hash, m, me)
        try:
            if not makeMove(gs, block): # 흑이 막을 자리가 금수
                return [m,block]
            try:
                sub = vcf(gs, depth - 1, nextHash(hash1, block, opp))
            finally:
                unmakeMove(gs) # 무르기는 반드시 실행
        finally:
            unmakeMove(gs)
        if sub: # VCF 수순
            return [m, block] + sub
    VCF_FAIL[hash] = depth
    return None

# 노드 수 제한을 두고 VCF 탐색
def findVCF(gs, hash, depth = VCF_DEPTH, limit = VCF_NODE_LIMIT):
    global vcfNodes, VCF_NODE_LIMIT
    vcfNodes, saved = 0, VCF_NODE_LIMIT
    VCF_NODE_LIMIT = limit
    try:
        return vcf(gs, depth, hash)
    except ThreatBudget:
        return None
    finally:
        VCF_NODE_LIMIT = saved

# 상대 차례라고 가정하고 상대의 VCF 를 찾음 (내가 한 수 쉬면 상대가 이기는지 = 상대의 위협)
def findOppVCF(gs, hash, depth = VCF_DEPTH, limit = VCF_NODE_LIMIT):
    gs.blackToPlay = not gs.blackToPlay
    try:
        return findVCF(gs, hash ^ ZOBRIST_SIDE, depth, limit)
    finally:
        gs.blackToPlay = not gs.blackToPlay

# 상대 VCF 를 막는 후보수만 남김
# 기존 후보 + 상대 VCF 수순 자리 (공격, 막기) + 나의 사(역공)
# 착수 했을 때 상대에게 VCF 가 없는 수만 선택
def filterByOppVCF(gs, hash, candidates, oppSeq):
    me = 'b' if gs.blackToPlay else 'w'
    pool = list(candidates)
    for m in oppSeq + findFourMoves(gs.board, me):
        if m not in pool and gs.board[m[0]][m[1]] == '-':
            pool.append(m)
    safe = []
    for m in pool:
        if not makeMove(gs, m):
            continue
        try:
            if gs.blackWin or gs.whiteWin or not findVCF(gs, nextHash(hash, m, me)):
                safe.append(m)
        finally:
            unmakeMove(gs)
    return safe if safe else candidates

# 리프 VCF 탐색 범위
VCF_LEAF_DEPTH = 4  # 리프에서 탐색할 사의 최대 개수
VCF_LEAF_LIMIT = 150 # 리프 VCF 한 번의 최대 노드 수

# 리프에서 차례인 쪽의 사를 만들 수 있는지 확인
# 만들 사가 없다면 VCF 탐색을 건너뜀
def leafHasFourChance(gs):
    if not incActive:
        return True
    c = incTotals['b' if gs.blackToPlay else 'w']
    return c[1] + c[2] + c[3] + c[4] > 0

'''
VCT 탐색 (Victory by Continuous Threats)
VCF 에 삼을 추가해서 계산함. 삼을 막는 위치가 여러 곳이기 때문에 VCF 보다 비용이 큼
상대의 모든 방어에 대해 내가 이길 수 있는 지 확인해야 함
비용이 크기 때문에 탐색 깊이와 노드 제한을 작게 둘 것임
공격 : 사 (막는 자리 1개), 삼 (다음 수에 열린 사 / 사-사 를 만들 수 있는 자리)
방어 : 삼을 막는 자리, 사 (역공)
'''
VCT_DEPTH = 4          # 공격 측 수(사 또는 삼)의 최대 개수 (사는 응수가 하나라 깊어도 괜찮지만, 삼이 많으면 급격히 느려짐)
VCT_NODE_LIMIT = 800  # VCT 한 번에 볼 최대 노드 수 (파이썬에서 약 0.5ms/노드)
VCT_FAIL = {}          # VCT_FAIL[해시] = 실패가 확인된 깊이
THREE_IDX_CACHE = {}   # (줄 문자열, 색) -> 그 줄에서 열린4 를 만들 수 있게 되는 자리 인덱스

# 삼 자리 찾기, 다음 수에 열린 사가 되면 삼 (위협)
def threeIndices(s, color):
    key = (s, color)
    r = THREE_IDX_CACHE.get(key)
    if r is None:
        r = []
        if s.count(color) >= 2:
            for i in range(len(s)):
                if s[i] != '-':
                    continue
                t = s[:i] + color + s[i+1:]
                if any(len(fiveIndices(t[:j] + color + t[j+1:], color)) >= 2
                       for j in range(len(t)) if t[j] == '-'):
                    r.append(i)
        r = tuple(r)
        THREE_IDX_CACHE[key] = r
    return r

def findThreeMoves(board, color):
    result = set()
    for idxLine, line in enumerate(LINES):
        for i in threeIndices(getLineStr(board, idxLine), color):
            result.add(line[i])
    return sorted(result)

# color 가 지금 두면 이기는 사 (오목 자리 2개 이상 : 열린4, 4-4). 흑은 금수를 제외
def findWinningFours(gs, color):
    board = gs.board
    result = []
    for m in findFourMoves(board, color):
        board[m[0]][m[1]] = color      # 잠깐 두어 보고 (fivesThrough 는 보드를 직접 읽음)
        n = len(fivesThrough(board, m, color))
        board[m[0]][m[1]] = '-'
        # 금수 판정은 느리므로 이기는 사인 경우에만 확인
        if n >= 2 and not (color == 'b' and gs.getForbiddenMove(m)):
            result.append(m)
    return result

# 공격 측(att) 의 삼을 막을 수 있는 자리 : 막은 뒤 att 가 이기는 사를 둘 수 없게 되는 자리만 남김
def findThreeDefenses(gs, att):
    board = gs.board
    wins = findWinningFours(gs, att)
    cand = set(wins)
    for w in wins: # 열린 사를 만드는 자리 + 그때 생기는 오목 자리 (삼의 양 끝)
        board[w[0]][w[1]] = att
        cand |= fivesThrough(board, w , att)
        board[w[0]][w[1]] = '-'
    defender = 'w' if att == 'b' else 'b'
    result = []
    for d in sorted(cand):
        if defender == 'b' and gs.getForbiddenMove(d):
            continue
        # d를 막은 뒤에도 기존의 이기는 사 중 하나라도 남아 있으면 방어 실패
        # 방어측 돌이 공격 측의 새로운 사를 만들 수 없으므로 기존 목록만 확인
        board[d[0]][d[1]] = defender
        ok = True
        for w in wins:
            if w == d:
                continue
            board[w[0]][w[1]] = att
            n = len(fivesThrough(board, w, att))
            board[w[0]][w[1]] = '-'
            if n >= 2:
                ok = False
                break
        board[d[0]][d[1]] = '-'
        if ok:
            result.append(d)
    return result


# 공격 차례. 이기는 수순을 찾으면 리스트 반환, 없으면 None
def vctAttack(gs, depth, hash):
    countTreatNode()
    me = 'b' if gs.blackToPlay else 'w'
    opp = 'w' if gs.blackToPlay else 'b'
    myFives = findFives(gs.board, me)
    if myFives:
        return [min(myFives)]
    if depth < 0:
        return None
    # 상대 공격을 막을 수 없으면 탐색x
    oppFives = findFives(gs.board, opp)
    if len(oppFives) >= 2:
        return None
    # 상대 사를 먼저 막아야함, 막는 수도 위협이어야 공격이 이어짐
    if oppFives:
        return vctAfterMove(gs, min(oppFives), depth, hash)
    if depth == 0 or VCT_FAIL.get(hash, -1) >= depth:
        return None
    fours = findFourMoves(gs.board, me)
    threes = [m for m in findThreeMoves(gs.board, me) if m not in fours]
    for m in fours + threes:
        r = vctAfterMove(gs, m , depth, hash)
        if r:
            return r
    VCT_FAIL[hash] = depth
    return None

# 공격이 m 에 둔 뒤 : 사이면 상대가 막고, 삼이면 상대의 모든 방어 확인
def vctAfterMove(gs, m, depth, h):
    me = 'b' if gs.blackToPlay else 'w'
    opp = 'w' if gs.blackToPlay else 'b'
    if not makeMove(gs, m):
        return None
    try:
        h1 = nextHash(h, m, me)
        fives = fivesThrough(gs.board, m, me)
        if len(fives) >= 2:
            return [m]
        if fives: # 사 : 상대는 막을 자리가 하나 뿐임
            block = min(fives)
            if not makeMove(gs, block): # 흑이 금수라 못막음
                return [m, block]
            try:
                sub = vctAttack(gs, depth-1, nextHash(h1, block, opp))
            finally:
                unmakeMove(gs)
            return [m, block] + sub if sub else None
        # 사가 아니면, 다음 수에 이기는 사를 둘 수 있어야 위협임
        if not findWinningFours(gs, me):
            return None
        sub = vctDefend(gs, depth - 1, h1)
        return [m] + sub if sub else None
    finally:
        unmakeMove(gs)

# 방어 측 차례 (공격은 다음수에 이기는 사를 둘 수 있는 상황). 모든 방어 실패시 공격 승리
def vctDefend(gs, depth, h):
    countTreatNode()
    me = 'b' if gs.blackToPlay else 'w'
    att = 'w' if gs.blackToPlay else 'b'
    if findFives(gs.board, me): # 방어측이 오목 있음 (공격실패)
        return None
    defenses = findThreeDefenses(gs, att) # 막는 자리 후보수
    for d in findFourMoves(gs.board, me): # 역공 후보수 (사는 무조건 막아야함)
        if d not in defenses:
            defenses.append(d)
    first = None
    for d in defenses:
        if not makeMove(gs, d):
            continue
        try:
            r = vctAttack(gs, depth, nextHash(h, d, me))
        finally:
            unmakeMove(gs)
        if not r:
            return None
        if first is None:
            first = [d] + r
    return first if first else ['(방어 불가)']

def findVCT(gs, h, depth = VCT_DEPTH, limit = VCT_NODE_LIMIT):
    global vcfNodes, VCF_NODE_LIMIT
    vcfNodes, saved = 0, VCF_NODE_LIMIT
    VCF_NODE_LIMIT = limit
    try:
        return vctAttack(gs, depth, h)
    except ThreatBudget:
        return None
    finally:
        VCF_NODE_LIMIT = saved

def findOppVCT(gs, h, depth = VCT_DEPTH, limit = VCT_NODE_LIMIT):
    gs.blackToPlay = not gs.blackToPlay
    try:
        return findVCT(gs, h ^ ZOBRIST_SIDE, depth, limit)
    finally:
        gs.blackToPlay = not gs.blackToPlay

# 상대 VCT 를 막는 후보만 남김 (두고 나서 상대에게 VCF, VCT 가 모두 없는 수)
def filterByOppVCT(gs, h, candidates, oppSeq):
    me = 'b' if gs.blackToPlay else 'w'
    opp = 'w' if gs.blackToPlay else 'b'
    pool = list(candidates)
    extra = [m for m in oppSeq if isinstance(m, tuple)] + findFourMoves(gs.board, me) + findThreeDefensesFor(gs, opp)
    for m in extra:
        if m not in pool and gs.board[m[0]][m[1]] == '-':
            pool.append(m)
    safe = []
    for m in pool:
        if not makeMove(gs, m):
            continue
        try:
            h1 = nextHash(h, m, me)
            if gs.blackWin or gs.whiteWin or not (findVCF(gs, h1) or findVCT(gs, h1, VCT_DEPTH, VCT_DEFENSE_LIMIT)):
                safe.append(m)
        finally:
            unmakeMove(gs)
    return safe if safe else candidates

VCT_DEFENSE_LIMIT = 300  # 방어 확인용 VCT 의 노드 제한 (후보마다 실행하므로 작게)

# 상대(opp)의 삼을 미리 막는 자리 (상대가 지금 열린4 를 만들 수 있으면 그 자리들)
def findThreeDefensesFor(gs, opp):
    if not findWinningFours(gs, opp):
        return []
    return findThreeDefenses(gs, opp)

# 루트탐색
# 이전 탐색의 최선 수 먼저 탐색
def searchRoot(gs, depth, candidates, firstMove, hash):
    # 이전 탐색의 최선 수를 후보수의 가장 앞에 배치함
    if firstMove in candidates:
        candidates = [firstMove] + [m for m in candidates if m != firstMove]
    color = 'b' if gs.blackToPlay else 'w' # hash
    alpha, beta = -float('inf'), float('inf')
    bestScore = -float('inf')
    bestPos = ()
    for move in candidates:
        if not makeMove(gs, move): # v2_3_incremental : placeStone->makeMove
            continue
        try:
            score, _ = negamax(gs, depth - 1, -beta, -alpha, nextHash(hash, move, color))
        finally:
            unmakeMove(gs) # v2_3_incremental : undoMove->unmakeMove
        score = -score
        if not bestPos or score > bestScore:
            bestScore = score
            bestPos = move
        alpha = max(alpha, score)
    return bestScore, bestPos

# ai는 백돌을 둔다
def aiMove(gs):
    if len(gs.moveLog) == 0: # 첫 수는 중앙
        return 7, 7

    # iterative deepening
    global nodeCount, searchDeadline, ttHits, incActive
    nodeCount = 0
    startTime = time.time()
    ttHits = 0

    # 전치표는 다음수에서 재사용, 크기 초과시 초기화
    if len(TT) > TT_MAX_SIZE:
        TT.clear()
    if len(CANDIDATE_CACHE) > TT_MAX_SIZE:
        CANDIDATE_CACHE.clear()
    hash = computeHash(gs)

    # 후보수
    candidates = getCandidateMoves(gs)
    if not candidates:
        return ()
    if len(candidates) == 1: # 강제수가 하나이면 탐색하지 않아도 됨
        print("AI 착수:", candidates[0], "(강제수)")
        return candidates[0]

    # 탐색
    incInit(gs) # 현재 보드로 증분상태 만들기
    try:
        return searchWithTreats(gs, hash, candidates, startTime)
    finally:
        # 탐색 종료시 증분상태 종료, 탐색 밖에서는 makeMove 없이 보드의 상태가 바뀌므로 상태가 맞지 않게 됨
        incActive = False



# aiMove 의 탐색 부분 분리 (코드 가독성)
def searchWithTreats(gs, hash, candidates, startTime):
    global searchDeadline
    searchDeadline = startTime + TIME_LIMIT

    # 내 VCF 가 있으면 탐색하지 않고 바로 둠
    mySeq = findVCF(gs, hash)
    if mySeq:
        print("AI 착수:", mySeq[0], "(VCF 승리 수순 :", mySeq, ')')
        return mySeq[0]

    # 상대 VCF 가 있으면 막는 수만 탐색함
    oppSeq = findOppVCF(gs, hash)
    if oppSeq:
        candidates = filterByOppVCF(gs, hash, candidates, oppSeq)
        print("상대 VCF 발견:", oppSeq, "-> 막는 후보:", candidates)
        if len(candidates) == 1:
            print("AI 착수:", candidates[0], "(VCF 방어)")
            return candidates[0]

    # 내 VCT 탐색 (비용이 크므로 전체 시간제한의 THREAT_TIME_RATIO 비율만큼)
    searchDeadline = startTime + TIME_LIMIT * THREAT_TIME_RATIO
    mySeq = findVCT(gs, hash)
    if mySeq:
        print("AI 착수:", mySeq[0], "(VCT 승리 수순:", mySeq, ")")
        return mySeq[0]

    # 상대 VCT 있으면 막는 수만 탐색
    if not oppSeq:
        oppSeq = findOppVCT(gs, hash)
        if oppSeq:
            candidates = filterByOppVCT(gs, hash, candidates, oppSeq)
            print("상대 VCT 발견:", oppSeq, "-> 막는 후보:", candidates)
            if len(candidates) == 1:
                print("AI 착수:", candidates[0], "(VCT 방어)")
                return candidates[0]
    # 기존 반복 심화 탐색 코드
    bestScore, bestPos, reachedDepth = 0, candidates[0], 0
    idStart = time.time() # 반복심화 탐색 시작한 시각
    for depth in range(1, MAX_DEPTH + 1):
        searchDeadline = float('inf') if depth == 1 else startTime + TIME_LIMIT  # 시작시각+제한시간
        try:
            score, pos = searchRoot(gs, depth, candidates, bestPos, hash)
        except SearchTimeout:  # 탐색 중간에 타임아웃 시 결과를 버림
            break
        if pos:
            bestScore, bestPos, reachedDepth = score, pos, depth
        # 이기거나 지는 수순 발견 시 더 이상 탐색하지 않음
        if abs(bestScore) >= WIN_THRESHOLD: # WIN_SCORE -> WIN_THRESHOLD (리프 VCF 에서 발견한 승리 처리)
            break
        # 다음 탐색을 시간 내에 못 끝낼 가능성이 매우 높으므로 탐색을 미리 중단함
        if time.time() - idStart > (startTime + TIME_LIMIT - idStart) / 2:
            break

    # 디버그 출력
    blackScore = bestScore if gs.blackToPlay else -bestScore
    print("AI 착수:", bestPos, "평가 점수:", blackScore,
          "깊이:", reachedDepth, "노드:", nodeCount, "전치표 사용:", ttHits,
          "시간: %.2f초" % (time.time() - startTime))  # 디버그용 출력
    return bestPos