package com.alexshabanov.sudoku;

import java.util.ArrayList;
import java.util.List;

/**
 * Entry point.
 */
public final class App {

    private static int SIZE = 9;

    private static int[][] createField() {
        final int[][] field = new int[SIZE][SIZE];

        /* 0 line */
        field[0][0] = 2;
        field[0][2] = 4;
        field[0][4] = 7;
        field[0][6] = 9;
        field[0][8] = 1;

        /* 1 line */

        /* 2 line */
        field[2][1] = 5;
        field[2][2] = 8;
        field[2][4] = 3;
        field[2][6] = 7;
        field[2][7] = 4;

        /* 3 line */
        field[3][3] = 9;
        field[3][5] = 7;

        /* 4 line */
        field[4][1] = 9;
        field[4][2] = 6;
        field[4][6] = 8;
        field[4][7] = 2;

        /* 5 line */
        field[5][3] = 5;
        field[5][5] = 2;

        /* 6 line */
        field[6][1] = 3;
        field[6][2] = 5;
        field[6][4] = 1;
        field[6][6] = 6;
        field[6][7] = 8;

        /* 7 line */

        /* 8 line */
        field[8][0] = 4;
        field[8][2] = 1;
        field[8][4] = 5;
        field[8][6] = 2;
        field[8][8] = 3;

        return field;
    }

    private static final class Coordinate {
        final int h;
        final int v;

        private Coordinate(int h, int v) {
            this.h = h;
            this.v = v;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Coordinate that = (Coordinate) o;

            if (h != that.h) return false;
            if (v != that.v) return false;

            return true;
        }

        @Override
        public int hashCode() {
            int result = h;
            result = 31 * result + v;
            return result;
        }

        @Override
        public String toString() {
            return "( " + h + " x " + v + " )";
        }
    }

    private static final List<Coordinate> findHollowCoordinates(int[][] field) {
        final List<Coordinate> coordinates = new ArrayList<Coordinate>();

        for (int i = 0; i < SIZE; ++i) {
            for (int j = 0; j < SIZE; ++j) {
                int c = field[i][j];
                if (c == 0) {
                    // this is an empty filed
                    coordinates.add(new Coordinate(j, i));
                }
            }
        }

        return coordinates;
    }

    private static void printField(int[][] field) {
        for (int i = 0; i < SIZE; ++i) {
            for (int j = 0; j < SIZE; ++j) {
                int c = field[i][j];
                if (c == 0) {
                    System.out.print(" .");
                } else {
                    System.out.print(" " + c);
                }
            }

            System.out.println();
        }

        System.out.println("---");
        System.out.flush();
    }

    private static final class Finder {
        static final int SQ_SIZE = 3;

        static {
            assert SIZE % SQ_SIZE == 0;
        }

        final int[] verFlags = new int[SIZE]; // vertical lines flags
        final int[] horFlags = new int[SIZE]; // horizontal lines flags

        final int[][] sqFlags = new int[SIZE / SQ_SIZE][SIZE / SQ_SIZE];

        final int[][] field;

        final List<Coordinate> coordinates;
        boolean printSolution;

        public void setPrintSolution(boolean printSolution) {
            this.printSolution = printSolution;
        }

        private void initHorFlags() {
            // fill horizontal flags
            for (int i = 0; i < SIZE; ++i) {
                int flag = 0;
                for (int j = 0; j < SIZE; ++j) {
                    final int c = field[i][j];

                    if (c == 0) {
                        continue;
                    }

                    final int f = 1 << c;
                    if ((flag & f) != 0) {
                        throw new AssertionError("Horizontal: duplicate entry at " + i + "x" + j + " num = " + c);
                    }
                    flag |= f;
                }
                horFlags[i] = flag;
            }
        }

        private void initVerFlags() {
            // fill vertical flags
            for (int j = 0; j < SIZE; ++j) {
                int flag = 0;
                for (int i = 0; i < SIZE; ++i) {
                    final int c = field[i][j];

                    if (c == 0) {
                        continue;
                    }

                    final int f = 1 << c;
                    if ((flag & f) != 0) {
                        throw new AssertionError("Vertical: duplicate entry at " + i + "x" + j + " num = " + c);
                    }
                    flag |= f;
                }
                verFlags[j] = flag;
            }
        }

        private void initSqFlags() {
            // fill squares
            for (int i = 0; i < SQ_SIZE; ++i) {
                for (int j = 0; j < SQ_SIZE; ++j) {
                    final int vStart = i * SQ_SIZE;
                    final int hStart = j * SQ_SIZE;

                    int flag = 0;
                    for (int lv = vStart; lv < (vStart + SQ_SIZE); ++lv) {
                        for (int lh = hStart; lh < (hStart + SQ_SIZE); ++lh) {
                            final int c = field[lv][lh];

                            if (c == 0) {
                                continue;
                            }

                            final int f = 1 << c;
                            if ((flag & f) != 0) {
                                throw new AssertionError("Square: duplicate entry at " + lv + "x" + lh + " num = " + c);
                            }
                            flag |= f;
                        }
                    }

                    sqFlags[i][j] = flag;
                }
            }
        }

        private Finder(int[][] field, List<Coordinate> coordinates) {
            this.field = field;
            this.coordinates = coordinates;

            initHorFlags();
            initVerFlags();
            initSqFlags();
        }

        void findSolution(int pos) {
            if (pos >= coordinates.size()) {
                if (printSolution) {
                    printField(field);
                }
                return;
            }

            Coordinate coord = coordinates.get(pos);

            for (int i = 1; i <= 9; ++i) {
                final int flag = 1 << i;

                // availability check
                if ((horFlags[coord.v] & flag) != 0 ||
                        (verFlags[coord.h] & flag) != 0 ||
                        (sqFlags[coord.v / SQ_SIZE][coord.h / SQ_SIZE] & flag) != 0) {
                    continue;
                }

                // set flags & field
                horFlags[coord.v] |= flag;
                verFlags[coord.h] |= flag;
                sqFlags[coord.v / SQ_SIZE][coord.h / SQ_SIZE] |= flag;

                field[coord.v][coord.h] = i;

                // proceed to the next one
                findSolution(pos + 1);

                // restore flags & field
                horFlags[coord.v] &= ~flag;
                verFlags[coord.h] &= ~flag;
                sqFlags[coord.v / SQ_SIZE][coord.h / SQ_SIZE] &= ~flag;

                field[coord.v][coord.h] = 0;
            }
        }
    }

    public static void main(String[] args) {
        System.out.println("Sudoku solution");

        final int[][] field = createField();
        printField(field);

        final List<Coordinate> coordinates = findHollowCoordinates(field);

        final Finder finder = new Finder(field, coordinates);

        final int RUN_TIMES = 16;
        // run test N times
        for (int i = 0; i < RUN_TIMES; ++i) {
            finder.setPrintSolution(i == 0);

            final long nanoStart = System.nanoTime();
            finder.findSolution(0);

            final long nanoTotal = System.nanoTime() - nanoStart;

            if (i == 0) {
                System.out.println("First pass - skipping measurement");
            } else {
                System.out.println("Total: " + nanoTotal + "ns");
            }
        }


        /*
        Correct answer is:
             2 6 4 8 7 5 9 3 1
             3 7 9 4 2 1 5 6 8
             1 5 8 6 3 9 7 4 2
             5 4 2 9 8 7 3 1 6
             7 9 6 1 4 3 8 2 5
             8 1 3 5 6 2 4 7 9
             9 3 5 2 1 4 6 8 7
             6 2 7 3 9 8 1 5 4
             4 8 1 7 5 6 2 9 3

mvn exec:java -Dexec.mainClass=com.alexshabanov.restcomp.client.App

Byte flags-driven solution:

Total: 15943000ns
Total: 12632000ns
Total: 9541000ns
Total: 8360000ns
Total: 499000ns
Total: 469000ns
Total: 463000ns
Total: 455000ns
Total: 458000ns
Total: 512000ns
Total: 447000ns
Total: 441000ns
Total: 434000ns
Total: 452000ns
Total: 442000ns

---
Unoptimized algorithm:

Total: 27200000ns
Total: 16537000ns
Total: 16916000ns
Total: 16843000ns
Total: 18861000ns
Total: 15885000ns
Total: 18556000ns
Total: 20794000ns
Total: 17180000ns

Best times:

18.556 vs 0.440 msec (18 msec is an approximate time for a nerve impulse to travel the length of a human)

=== gcc (comparison to C implementation) - gcc -O0 -g -Wall -std=c99 main.c  -o m:

 2 6 4 8 7 5 9 3 1
 3 7 9 4 2 1 5 6 8
 1 5 8 6 3 9 7 4 2
 5 4 2 9 8 7 3 1 6
 7 9 6 1 4 3 8 2 5
 8 1 3 5 6 2 4 7 9
 9 3 5 2 1 4 6 8 7
 6 2 7 3 9 8 1 5 4
 4 8 1 7 5 6 2 9 3
0 Elapsed time: 1010000 nanoseconds
1 Elapsed time: 887000 nanoseconds
2 Elapsed time: 885000 nanoseconds
3 Elapsed time: 852000 nanoseconds
4 Elapsed time: 836000 nanoseconds
5 Elapsed time: 842000 nanoseconds
6 Elapsed time: 853000 nanoseconds
7 Elapsed time: 884000 nanoseconds
8 Elapsed time: 879000 nanoseconds
9 Elapsed time: 825000 nanoseconds
10 Elapsed time: 834000 nanoseconds
11 Elapsed time: 858000 nanoseconds
12 Elapsed time: 874000 nanoseconds
13 Elapsed time: 880000 nanoseconds
14 Elapsed time: 835000 nanoseconds
15 Elapsed time: 835000 nanoseconds


Results with gcc -O3 -Wall -std=c99 main.c  -o m
 2 6 4 8 7 5 9 3 1
 3 7 9 4 2 1 5 6 8
 1 5 8 6 3 9 7 4 2
 5 4 2 9 8 7 3 1 6
 7 9 6 1 4 3 8 2 5
 8 1 3 5 6 2 4 7 9
 9 3 5 2 1 4 6 8 7
 6 2 7 3 9 8 1 5 4
 4 8 1 7 5 6 2 9 3
0 Elapsed time: 877000 nanoseconds
1 Elapsed time: 731000 nanoseconds
2 Elapsed time: 726000 nanoseconds
3 Elapsed time: 678000 nanoseconds
4 Elapsed time: 572000 nanoseconds
5 Elapsed time: 584000 nanoseconds
6 Elapsed time: 572000 nanoseconds
7 Elapsed time: 571000 nanoseconds
8 Elapsed time: 572000 nanoseconds
9 Elapsed time: 586000 nanoseconds
10 Elapsed time: 549000 nanoseconds
11 Elapsed time: 486000 nanoseconds
12 Elapsed time: 486000 nanoseconds
13 Elapsed time: 486000 nanoseconds
14 Elapsed time: 488000 nanoseconds
15 Elapsed time: 471000 nanoseconds
         */
    }
}
