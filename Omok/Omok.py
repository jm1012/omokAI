'''
main file
'''
import pygame as pg
import OmokEngine
import OmokAI as ai
import OmokAI_v2 as ai2

WIDTH = HEIGHT = 600
DIMENSION = 15
SQ_SIZE = WIDTH//DIMENSION
IMAGES = {}

def loadImages():
    IMAGES['w'] = pg.transform.scale(pg.image.load('images/white_stone_simple.png'), (SQ_SIZE, SQ_SIZE))
    IMAGES['b'] = pg.transform.scale(pg.image.load('images/black_stone_simple.png'), (SQ_SIZE, SQ_SIZE))
    IMAGES['f'] = pg.transform.scale(pg.image.load('images/forbidden_mark.png'), (SQ_SIZE, SQ_SIZE))

def main():
    # drawing board
    pg.init()
    loadImages()
    screen = pg.display.set_mode((WIDTH, HEIGHT))
    screen.fill(pg.Color(220,220,220))
    squareSelected = ()
    gs = OmokEngine.GameState()
    drawGameState(screen, gs)
    debugMode = False # 디버깅

    running = True
    while running:
        # computer's turn
        if not gs.blackToPlay and not debugMode:
            computerMove(gs, ai2)
            continue
        # user's turn
        for event in pg.event.get():
            if event.type == pg.QUIT:
                running = False
            # mouse handler
            elif event.type == pg.MOUSEBUTTONDOWN:
                location = event.pos
                x = int (location[0] + 0.5 * SQ_SIZE) // SQ_SIZE
                y = int (location[1] + 0.5 * SQ_SIZE) // SQ_SIZE
                squareSelected = (x,y)
                print(squareSelected)
                if not (0 <= x < DIMENSION and 0 <= y < DIMENSION):
                    continue
                # 선택한 칸이 빈칸이면 착수
                if gs.board[x][y] == '-':
                    if not gs.placeStone(squareSelected):
                        print("해당 자리는 금수입니다")
            # keyboard handler
            elif event.type == pg.KEYDOWN:
                if event.key == pg.K_z: # undo move
                    gs.undoMove()
                    if debugMode == False:
                        gs.undoMove()
                elif event.key == pg.K_d: # debug
                    if debugMode:  print("debug mode : False")
                    else:           print ("debug mode : True")
                    debugMode = not debugMode
        if gs.blackWin or gs.whiteWin: # 게임 종료
            winner = "black" if gs.blackWin else "white"
            print(winner + " win!")
            gs.saveMoveLog() # 로그 저장
            running = False
        # draw board
        drawGameState(screen, gs)

# 오목 봇 버전을 선택 (성능 비교 용)
def computerMove(gs, botVersion):
    pos = botVersion.aiMove(gs)
    if not pos:  # 빈 튜플 방어
        return False
    gs.placeStone(pos)
    return True

def drawGameState(screen, gs):
    drawBoard(screen)
    drawStone(screen, gs)
    pg.display.flip()

def drawBoard(screen):
    screen.fill(pg.Color(220, 220, 220))
    lineColor = (0,0,0)
    for x in range(0, WIDTH, SQ_SIZE):
        pg.draw.line(screen, lineColor, (x, 0), (x, HEIGHT))
    for y in range(0, HEIGHT, SQ_SIZE):
        pg.draw.line(screen, lineColor, (0, y), (WIDTH, y))

def drawStone(screen, gs):
    for x in range(0, DIMENSION):
        for y in range(0, DIMENSION):
            if gs.board[x][y] == 'w':
                screen.blit(IMAGES['w'], pg.Rect((x - 0.5) * SQ_SIZE, (y - 0.5) * SQ_SIZE, SQ_SIZE, SQ_SIZE))
            elif gs.board[x][y] == 'b':
                screen.blit(IMAGES['b'], pg.Rect((x - 0.5) * SQ_SIZE, (y - 0.5) * SQ_SIZE, SQ_SIZE, SQ_SIZE))
            elif gs.board[x][y] == 'f':
                screen.blit(IMAGES['f'], pg.Rect((x - 0.5) * SQ_SIZE, (y - 0.5) * SQ_SIZE, SQ_SIZE, SQ_SIZE))

if __name__ == "__main__":
    main()