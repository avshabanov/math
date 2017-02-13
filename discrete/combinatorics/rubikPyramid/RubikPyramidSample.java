
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Shabanov
 */
public final class RubikPyramidSample {

  public static void main(String[] args) throws IOException {
    demo();
    demo1();
    System.out.println();
    System.out.println();
    System.out.println();
    System.out.flush();
  }

  private static void demo() throws IOException {
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

  private static void demo1() throws IOException {
    final Pyramid pyramid = new Pyramid();
    pyramid
        .setState(1, 27 + 1)
        .setState(9 + 6, 18 + 6)
        .setState(18 + 6, 9 + 6)
        .setState(27 + 1, 1);
    pyramid.printTo("demo1", System.out);

    trySolve(pyramid);
  }

  private static void trySolve(Pyramid pyramid) {
    final Solver solver = new Solver(pyramid, 5);
    if (solver.solve()) {
      System.out.println("Solution found: " + solver.solution);
    } else {
      System.out.println("Solution has not been found, try increase depth. " +
          solver.combinations + " combination(s) tried");
    }
  }

  private static final class Solver {
    final Pyramid pyramid;
    List<Integer> solution;
    final List<Integer> vertexRotations = new ArrayList<>();
    final int maxDepth;
    int combinations;

    public Solver(Pyramid pyramid, int maxDepth) {
      this.pyramid = pyramid;
      this.maxDepth = maxDepth;
    }

    public boolean solve() {
      return solve(0);
    }

    public boolean solve(int depth) {
      ++combinations;

      final int vertexRotationsSize = vertexRotations.size();
      boolean solved = true;
      for (int i = 0; i < pyramid.state.length; ++i) {
        if (pyramid.state[i] != i) {
          solved = false;
          break;
        }
      }

      if (solved) {
        if (solution == null || solution.size() > vertexRotationsSize) {
          solution = new ArrayList<>(vertexRotations); // copy current rotations - it leads to solution
        }
        return true;
      }

      if (depth >= maxDepth) {
        return false;
      }

      //final int previousRotation = vertexRotations.isEmpty() ? 0 : vertexRotations.get(vertexRotationsSize - 1);
      for (int i = 1; i <= 4; ++i) {
        vertexRotations.add(i);
        pyramid.rotate(i);
        solved = solve(depth + 1);
        pyramid.rotate(-i); // restore
        vertexRotations.remove(vertexRotations.size() - 1); // TODO: fix
        if (solved) {
          return true;
        }

        // TODO: remove duplication
        vertexRotations.add(-i);
        pyramid.rotate(-i);
        solved = solve(depth + 1);
        pyramid.rotate(i); // restore
        vertexRotations.remove(vertexRotations.size() - 1);
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

    public Pyramid setState(int pos, int value) {
      this.state[pos] = value;
      return this;
    }

    public void loadIdentity() {
      for (int i = 0; i < state.length; ++i) {
        state[i] = i;
      }
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

    public void printTo(String name, PrintStream out) throws IOException {
      out.println();
      out.println("Pyramid " + name + ":");
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
