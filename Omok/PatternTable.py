'''
패턴 테이블
칸 하나 x 방향 하나 마다, 그 칸 주변 +-7 칸(14칸)의 상태를 정수 하나(코드)로 저장한다.
칸 상태 : 0 빈칸, 1 흑, 2 백, 3 벽(보드 밖)  -> 2비트씩 14칸 = 28비트
TABLE[차례][코드] = 그 칸에 차례인 쪽이 두었을 때의 패턴 변화 (한 번 계산하면 저장)
'''
DIRECTIONS = [(1, 0), (0, 1), (1, 1), (1, -1)]  # OmokAI 와 같은 순서여야 함
BOARD_SIZE = 15
countLinePatterns = None  # setup() 으로 OmokAI 의 함수를 받아옴 (순환 import 방지)


def setup(countFn):
    global countLinePatterns
    countLinePatterns = countFn


RADIUS = 7  # 6 이하로 줄이면 열린 2/3 판정이 창 끝에서 잘려 결과가 달라짐 (측정: 5칸 1~7%, 6칸 0.2% 불일치)
OFFSETS = [k for k in range(-RADIUS, RADIUS + 1) if k != 0]  # -5..-1, 1..5
SLOT = {k: i for i, k in enumerate(OFFSETS)}  # 오프셋 -> 비트 위치(0~9)
VAL = {'-': 0, 'b': 1, 'w': 2}
CH = '-bw#'


# codes[x][y][d] : 칸 (x,y), 방향 d 의 코드
def initCodes(board):
    codes = [[[0] * 4 for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]
    for x in range(BOARD_SIZE):
        for y in range(BOARD_SIZE):
            for d, (dx, dy) in enumerate(DIRECTIONS):
                c = 0
                for k in OFFSETS:
                    nx, ny = x + dx * k, y + dy * k
                    v = VAL[board[nx][ny]] if 0 <= nx < BOARD_SIZE and 0 <= ny < BOARD_SIZE else 3
                    c |= v << (2 * SLOT[k])
                codes[x][y][d] = c
    return codes


# (x,y) 에 color 를 두거나(place) 무를 때(undo) 주변 코드 갱신 : 빈칸(0) <-> 돌(1,2) 이므로 xor 하나면 됨
def updateCodes(codes, pos, color):
    x, y = pos
    v = VAL[color]
    for d, (dx, dy) in enumerate(DIRECTIONS):
        for k in OFFSETS:
            nx, ny = x - dx * k, y - dy * k  # (nx,ny) 에서 보면 pos 는 오프셋 +k 위치
            if 0 <= nx < BOARD_SIZE and 0 <= ny < BOARD_SIZE:
                codes[nx][ny][d] ^= v << (2 * SLOT[k])


def windowStr(code, center):
    left = ''.join(CH[(code >> (2 * SLOT[k])) & 3] for k in OFFSETS if k < 0)
    right = ''.join(CH[(code >> (2 * SLOT[k])) & 3] for k in OFFSETS if k > 0)
    return left + center + right


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


# 표의 한 칸 계산 : 기존 countLinePatterns 를 그대로 재사용함 (규칙이 같아야 하므로)
def computeEntry(code, me):
    opp = 'w' if me == 'b' else 'b'
    before = windowStr(code, '-')
    mine = windowStr(code, me)
    theirs = windowStr(code, opp)
    meDelta = sub(countLinePatterns(mine, me), countLinePatterns(before, me))  # 내가 두면 생기는 내 패턴
    oppDelta = sub(countLinePatterns(theirs, opp), countLinePatterns(before, opp))  # 상대가 두면 생기는 상대 패턴
    oppLoss = sub(countLinePatterns(mine, opp), countLinePatterns(before, opp))  # 내가 두면 줄어드는 상대 패턴
    # 흑 장목 : 가운데를 포함한 연속 흑돌이 6개 이상
    run = 1
    for step in (-1, 1):
        k = step
        while -RADIUS <= k <= RADIUS and (code >> (2 * SLOT[k])) & 3 == 1:
            run += 1;
            k += step
    overline = me == 'b' and run >= 6
    return meDelta, oppDelta, oppLoss, overline


TABLE = {'b': {}, 'w': {}}  # 처음 보는 코드만 계산하고 저장 (지연 생성)


def lookup(code, me):
    t = TABLE[me]
    e = t.get(code)
    if e is None:
        e = t[code] = computeEntry(code, me)
    return e


# 흑 금수 판정 (표 이용)
def isForbiddenByTable(codes, pos):
    x, y = pos
    threes = fours = 0
    for d in range(4):
        meDelta, _, _, overline = lookup(codes[x][y][d], 'b')
        if meDelta[0] > 0:  # 오목이 되면 금수 아님
            return False
        if overline:
            return True
        if meDelta[3] > 0:
            threes += 1
        fours += max(0, meDelta[1] + meDelta[2])
    return threes >= 2 or fours >= 2
