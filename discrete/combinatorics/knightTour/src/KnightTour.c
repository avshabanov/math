#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include <sys/time.h>

#define DEFAULT_BOARD_SIDE_SIZE     (8)
#define DEFAULT_START_ROW           (0)
#define DEFAULT_START_COLUMN        (0)
#define DEFAULT_ITERATIONS          (1)

struct Move {
    int rowDelta;
    int columnDelta;
};

static struct Move g_knightMoves[] = {
    {2, 1}, {1, 2}, {-1, 2}, {-2, 1}, {-2, -1}, {-1, -2}, {1, -2}, {2, -1}
};

struct SolutionFinder {
    int rows;
    int columns;
    int * board;
    int maxMoves;
};

#define BOARD_AT(finder, row, column) \
    (*((finder)->board + row * (finder)->columns + column))

static void
initSolutionFinder(struct SolutionFinder * finder, int columns, int rows) {
    int boardSize = rows * columns * sizeof(int);

    finder->columns = columns;
    finder->rows = rows;
    finder->board = malloc((size_t) boardSize);
    memset(finder->board, 0, boardSize);
    finder->maxMoves = rows * columns;
}

static bool
isLegalMove(struct SolutionFinder * finder, int row, int column) {
    return row >= 0 && column >= 0 && row < finder->rows && column < finder->columns &&
        BOARD_AT(finder, row, column) == 0;
}

static bool
makeMove(struct SolutionFinder * finder, int currentRow, int currentColumn, int currentMoveIndex) {
    BOARD_AT(finder, currentRow, currentColumn) = currentMoveIndex;

    if (currentMoveIndex >= finder->maxMoves) {
        // solution found
        return true;
    }

    for (int i = 0; i < 8; ++i) {
        struct Move * move = g_knightMoves + i;
        int nextRow = currentRow + move->rowDelta;
        int nextColumn = currentColumn + move->columnDelta;
        if (isLegalMove(finder, nextRow, nextColumn) &&
            makeMove(finder, nextRow, nextColumn, currentMoveIndex + 1)) {
            return true;
        }
    }

    // this move is not a valid one, reset current mark
    BOARD_AT(finder, currentRow, currentColumn) = 0;
    return false;
}

static void
printBoard(struct SolutionFinder * finder) {
    printf("board:\n");
    for (int row = 0; row < finder->rows; ++row) {
        for (int column = 0; column < finder->columns; ++column) {
            printf(" %3d", BOARD_AT(finder, row, column));
        }
        printf("\n");
    }
}

static void
closeSolutionFinder(struct SolutionFinder * finder) {
    free(finder->board);
}

#define NANO_UNIT       (1000000000LL)

static void printFormattedNanoTime(long long nanoTime, FILE * os) {
    long long sec = nanoTime / NANO_UNIT;
    long long nanos = (nanoTime - (sec * NANO_UNIT));
    fprintf(os, "%lld sec %06lld %03lld msec", sec, nanos / 1000, nanos % 1000);
}

static void
findSolution(int rows, int columns, int startRow, int startColumn) {
    struct SolutionFinder finder;
    struct timeval start;
    struct timeval stop;
    bool found;

    initSolutionFinder(&finder, rows, columns);
    gettimeofday(&start, NULL);
    found = makeMove(&finder, startRow, startColumn, 1);
    gettimeofday(&stop, NULL);

    long long nanoTime = (stop.tv_sec - start.tv_sec) * NANO_UNIT + (stop.tv_usec - start.tv_usec) * 1000L;
    printf("Solution ");
    if (found) {
        printf("found: ");
        printBoard(&finder);
    } else {
        printf("not found");
    }
    printf("\nTime: ");
    printFormattedNanoTime(nanoTime, stdout);
    printf("\n\n");

    closeSolutionFinder(&finder);
}

static int 
getArgParam(char ** argv, int argc, int index, int defaultValue) {
    return index < argc ? atoi(argv[index]) : defaultValue;
}

int main(int argc, char ** argv) {
    int rows = getArgParam(argv, argc, 1, DEFAULT_BOARD_SIDE_SIZE);
    int columns = getArgParam(argv, argc, 2, DEFAULT_BOARD_SIDE_SIZE);
    int iterations = getArgParam(argv, argc, 3, DEFAULT_ITERATIONS);

    printf("KnightTour {rows} {columns} {iterations}\n"
           "Using rows=%d, columns=%d and iterations=%d\n",
           rows, columns, iterations);

    for (int j = 0; j < iterations; ++j) {
        findSolution(rows, columns, DEFAULT_START_ROW, DEFAULT_START_COLUMN);
    }

    return 0;
}

