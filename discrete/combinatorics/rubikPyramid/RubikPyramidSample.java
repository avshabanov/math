
import java.io.IOException;
import java.io.PrintStream;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * @author Alexander Shabanov
 */
public final class RubikPyramidSample {

  public static void main(String[] args) {
    final String mode = System.getProperty("RubikPyramidSample.demo", "3");
    switch (mode) {
      case "1":
        demo1();
        break;

      case "2":
        demo2();
        break;

      case "3":
        demo3();
        break;

      default:
        demo();
    }
  }

  private static void demo() {
    final Pyramid pyramid = new Pyramid();
    pyramid.printTo("id0", System.out);

    pyramid.rotate(1);
    pyramid.printTo("id1", System.out);

    pyramid.rotate(-1);
    pyramid.printTo("id2", System.out);

//    pyramid.rotate(0, false);
//    pyramid.printTo("id3", System.out);

    pyramid.rotate(4);
    pyramid.printTo("id4", System.out);
  }

  private static void demo1() {
    final Pyramid pyramid = new Pyramid();
    pyramid.rotate(1);
    pyramid.rotate(2);
    pyramid.rotate(-1);
    pyramid.rotate(-2);
    pyramid.printTo("demo1", System.out);

    trySolve(pyramid, 4);
  }

  private static void demo2() {
    final Pyramid pyramid = new Pyramid();
    pyramid.setState(1, 27 + 1);
    pyramid.setState(9 + 6, 18 + 6);
    pyramid.setState(18 + 6, 9 + 6);
    pyramid.setState(27 + 1, 1);
    pyramid.printTo("demo2", System.out);

    trySolve(pyramid, 5);
  }

  private static void demo3() {
    final Pyramid pyramid = new Pyramid();
    pyramid.rotate(1);
    pyramid.rotate(2);
    pyramid.rotate(3);
    pyramid.rotate(-4);
    pyramid.rotate(-2);
    pyramid.rotate(1);
    pyramid.rotate(-3);
    pyramid.printTo("demo3", System.out);

    trySolve(pyramid, 7);
  }

  private static void trySolve(Pyramid pyramid, int maxDepth) {
    final Solver solver = new Solver(pyramid, maxDepth);
    long timeDelta = System.currentTimeMillis();
    if (solver.solve()) {
      timeDelta = System.currentTimeMillis() - timeDelta;
      System.out.println("[" + timeDelta + "ms] Solution found: " + solver.solution);

      // explain solution
      for (int i = 0; i < solver.solution.size(); ++i) {
        final int vertexRotation = solver.solution.get(i);
        pyramid.rotate(vertexRotation);
        pyramid.printTo("Move #" + i + ": vertexRotation=" + vertexRotation, System.out);
      }

    } else {
      timeDelta = System.currentTimeMillis() - timeDelta;
      System.out.println("[" + timeDelta + "ms] Solution has not been found, try increase depth. " +
          solver.combinations + " combination(s) tried");
    }
  }

  private static final class Solver {
    final Pyramid pyramid;
    List<Integer> solution;
    final int[] vertexRotations;
    int vertexRotationsSize;
    int combinations;

    public Solver(Pyramid pyramid, int maxDepth) {
      this.pyramid = pyramid;
      this.vertexRotations = new int[maxDepth];
    }

    public boolean solve() {
      return solve(0);
    }

    public boolean solve(int depth) {
      ++combinations;

      boolean solved = pyramid.isSimilarToIdentity();
      if (solved) {
        if (solution == null || solution.size() > vertexRotationsSize) {
          // copy current rotations as they form a solution
          solution = IntStream.of(vertexRotations).limit(vertexRotationsSize).boxed().collect(Collectors.toList());
        }
        return true;
      }

      if (depth >= vertexRotations.length) {
        return false;
      }

      final int previousRotation = vertexRotationsSize > 0 ? vertexRotations[vertexRotationsSize - 1] : 0;
      for (int i = -4; i <= 4; ++i) {
        // skip dummy rotations
        if (i == 0 ||
            previousRotation == -i ||
            (previousRotation == i && vertexRotationsSize > 2 && vertexRotations[vertexRotationsSize - 2] == i)) {
          continue;
        }

        vertexRotations[vertexRotationsSize] = i;
        ++vertexRotationsSize;
        pyramid.rotate(i);
        solved = solve(depth + 1);
        pyramid.rotate(-i); // restore pyramid state
        --vertexRotationsSize;
        if (solved) {
          return true;
        }
      }

      return false; // pyramid is in impossible positions
    }
  }

  //
  // Private
  //

  private static final class Pyramid {
    private static final int CELL_ROWS = 3;
    private static final int SIDES = 4;
    private static final int CELLS_ON_SIDE = CELL_ROWS * CELL_ROWS;
    private static final int IDENT_SPACE = 4;

    private static final String SIDE_COLORS = "rygb";

    private static final String ANSI_RESET = "\u001B[0m";
    private static final String ANSI_RED = "\u001B[31m";
    private static final String ANSI_GREEN = "\u001B[32m";
    private static final String ANSI_YELLOW = "\u001B[33m";
    private static final String ANSI_BLUE = "\u001B[34m";
//    private static final String ANSI_BLACK = "\u001B[30m";
//    private static final String ANSI_PURPLE = "\u001B[35m";
//    private static final String ANSI_CYAN = "\u001B[36m";
//    private static final String ANSI_WHITE = "\u001B[37m";

    private static final String[] ANSI_SIDE_COLOR_STR = {
        ANSI_RED,
        ANSI_YELLOW,
        ANSI_GREEN,
        ANSI_BLUE
    };

    /**
     * Structure:
     * Every 1+3+5 = 9 cells on each side and there are 4 sides in total.
     */
    final int state[] = new int[CELLS_ON_SIDE * SIDES];

    public Pyramid() {
      loadIdentity();
    }

    public void setState(int pos, int value) {
      this.state[pos] = value;
    }

    public void loadIdentity() {
      for (int i = 0; i < state.length; ++i) {
        state[i] = i;
      }
    }

    public boolean isSimilarToIdentity() {
      for (int side = 0; side < SIDES; ++side) {
        final int start = CELLS_ON_SIDE * side;
        for (int cell = 1; cell < CELLS_ON_SIDE; ++cell) {
          final int cellIndex = start + cell;
          if ((this.state[cellIndex - 1] + 1) != this.state[cellIndex]) {
            return false;
          }
        }
      }
      return true;
    }

    public void rotate(int vertexRotation) {
      final boolean clockwise;
      final int vertex;
      if (vertexRotation < 0) {
        clockwise = false;
        vertex = -vertexRotation;
      } else {
        clockwise = true;
        vertex = vertexRotation;
      }
      assert vertex >= 1 && vertex <= SIDES;

      // TODO: better work with constants
      // red: 0, yellow:9, green: 18, blue: 27
      switch (vertex) {
        case 1: // red-yellow-green
          swap3(0, 9/* + 0*/, 18/*+ 0*/, clockwise);
          swap3(1, 9 + 1, 18 + 1, clockwise);
          swap3(2, 9 + 2, 18 + 2, clockwise);
          swap3(3, 9 + 3, 18 + 3, clockwise);
          break;
        case 2: // red-yellow-blue
          swap3(3, 9 + 6, 27 + 6, clockwise);
          swap3(6, 9 + 1, 27 + 1, clockwise);
          swap3(7, 9 + 5, 27 + 5, clockwise);
          swap3(8, 9 + 4, 27 + 4, clockwise);
          break;
        case 3: // red-green-blue
          swap3(1, 18 + 6, 27 + 6, clockwise);
          swap3(4, 18 + 8, 27 + 8, clockwise);
          swap3(5, 18 + 7, 27 + 7, clockwise);
          swap3(6, 18 + 3, 27 + 3, clockwise);
          break;
        case 4: // yellow-green-blue
          swap3(9 + 3, 18 + 6, 27 + 1, clockwise);
          swap3(9 + 6, 18 + 1, 27 + 3, clockwise);
          swap3(9 + 7, 18 + 5, 27 + 2, clockwise);
          swap3(9 + 8, 18 + 4, 27/* + 0*/, clockwise);
          break;
        default:
          throw new IllegalArgumentException("vertex");
      }
    }

    private void swap3(int pos1, int pos2, int pos3, boolean clockwise) {
      final int temp = state[pos1];
      if (clockwise) {
        state[pos1] = state[pos3];
        state[pos3] = state[pos2];
        state[pos2] = temp;
      } else {
        state[pos1] = state[pos2];
        state[pos2] = state[pos3];
        state[pos3] = temp;
      }
    }

    public void printTo(String name, PrintStream out) {
      try {
        printToOutputStream(name, out);
      } catch (IOException e) {
        throw new IllegalStateException(e);
      }
    }

    private void printToOutputStream(String name, PrintStream out) throws IOException {
      out.println();
      out.println("Pyramid " + name + " (identitySimilarity=" + isSimilarToIdentity() + "):");
      for (int row = 0; row < CELL_ROWS; ++row) {
        for (int side = 0; side < SIDES; ++side) {
          final int start = CELLS_ON_SIDE * side;
          final int ident = (IDENT_SPACE * (CELL_ROWS - row - 1));
          printIdent(out, ident);

          // print row
          for (int i = start + row * row; i < start + row * row + 2 * row + 1; ++i) {
            out.print(cellToString(state[i]));
          }

          printIdent(out, ident);
          out.print('|');
        }

        out.println();
      }
    }

    private static void printIdent(PrintStream out, int count) throws IOException {
      for (int i = 0; i < count; ++i) {
        out.print(' ');
      }
    }

    private static String cellToString(int cellValue) {
      final int color = cellValue / CELLS_ON_SIDE;
      final int index = cellValue % CELLS_ON_SIDE;
      return " " + ANSI_SIDE_COLOR_STR[color] + SIDE_COLORS.charAt(color) + index + ANSI_RESET + " ";
    }
  }
}
