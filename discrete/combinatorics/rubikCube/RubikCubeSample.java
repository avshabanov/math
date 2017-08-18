import java.io.IOException;
import java.io.PrintStream;
import java.util.*;

/**
 * @author Alexander Shabanov
 */
public class RubikCubeSample {

  public static void main(String[] args) throws IOException {
    if (args.length > 0 && args[0].equals("1")) {
      demo1();
    } else {
      demo2();
    }
  }

  static void demo2() throws IOException {
    System.out.println("RubikState #2:");
    RubikCube2State s = new RubikCube2State();
    s
        .loadIdentity()
        .rotate(0)
        .rotate(5)
        .print(System.out).printIfAssembled(System.out);

    s.findSolution(System.out);

    System.out.println();
  }

  static void demo1() throws IOException {
    System.out.println("Sample Rubik State:");
    RubikCube2State s = new RubikCube2State();
    s
        .loadIdentity()
        .print(System.out).printIfAssembled(System.out)
        .rotate(0)
        .print(System.out).printIfAssembled(System.out)
        .rotate(2)
        .print(System.out).printIfAssembled(System.out)
        .rotate(3)
        .print(System.out).printIfAssembled(System.out)
        .rotate(1)
        .print(System.out).printIfAssembled(System.out);
    System.out.println();
  }

  static final class TransformationBuilder {
    Map<Integer, Integer> directTransformation = new HashMap<>();
    Map<Integer, Integer> oppositeTransformation = new HashMap<>();

    TransformationBuilder add(int from, int to) {
      if (from == to) {
        throw new IllegalArgumentException("Same args");
      }

      if (directTransformation.put(from, to) != null) {
        throw new IllegalArgumentException("Duplicate from=" + from);
      }

      if (oppositeTransformation.put(to, from) != null) {
        throw new IllegalArgumentException("Duplicate to=" + to);
      }

      return this;
    }

    List<int[]> buildMoveIndices() {
      final List<int[]> result = new ArrayList<>();
      result.add(buildMoveIndices(directTransformation, RubikCube2State.CELLS));
      result.add(buildMoveIndices(oppositeTransformation, RubikCube2State.CELLS));
      return result;
    }

    static int[] buildMoveIndices(Map<Integer, Integer> transformation, int maxSize) {
      final int[] result = new int[maxSize];

      for (int i = 0; i < maxSize; ++i) {
        final Integer targetIndex = transformation.get(i);
        result[i] = targetIndex != null ? targetIndex : i;
      }

      // validate:
      for (int i = 0; i < maxSize; ++i) {
        boolean present = false;

        for (int j = 0; j < maxSize; ++j) {
          if (result[j] == i) {
            present = true;
            break;
          }
        }

        if (!present) {
          throw new IllegalArgumentException("Misplaced target index for position=" + i);
        }
      }

      return result;
    }
  }

  /**
   * Rubik Cube 2x2x2.
   * Color encodings as per https://upload.wikimedia.org/wikipedia/commons/thumb/b/b9/Western_color_scheme_of_a_Rubik%27s_Cube.svg/306px-Western_color_scheme_of_a_Rubik%27s_Cube.svg.png
   *
   * <pre>
   *             [0:ORANGE]
   *  [1:YELLOW] [1:GREEN]  [2:WHITE]
   *              [3:RED]
   *              [4:CYAN]
   * </pre>
   */
  static final class RubikCube2State {
    static final int CL_ORANGE = 0;
    static final int CL_YELLOW = 1;
    static final int CL_GREEN = 2;
    static final int CL_WHITE = 3;
    static final int CL_RED = 4;
    static final int CL_CYAN = 5;

    static final String COLOR_CODE = "OYGWRC";

    static final int DIM = 2;
    static final int SIDES = 6;
    static final int CELLS = SIDES * DIM * DIM;
    int state[] = new int[CELLS];

    static final List<int[]> TRANSFORMATION_MOVES = new ArrayList<int[]>() {
      {
        // Move #1 and #2
        addAll(new TransformationBuilder()
            .add(0, 8).add(2, 10).add(8, 16).add(10, 18).add(16, 20).add(18, 22).add(20, 0).add(22, 2)
            .add(4, 6).add(5, 4).add(6, 7).add(7, 5)
            .buildMoveIndices());

        // Move #3 and #4
        addAll(new TransformationBuilder()
            .add(1, 9).add(3, 11).add(9, 17).add(11, 19).add(17, 21).add(19, 23).add(21, 1).add(23, 3)
            .add(12, 13).add(13, 15).add(14, 12).add(15, 14)
            .buildMoveIndices());

        // Move #5 and #6
        addAll(new TransformationBuilder()
            .add(0, 13).add(1, 15).add(13, 19).add(15, 18).add(19, 6).add(18, 4).add(6, 0).add(4, 1)
            .add(23, 22).add(22, 20).add(21, 23).add(20, 21)
            .buildMoveIndices());

        // Move #7 and #8
        addAll(new TransformationBuilder()
            .add(2, 12).add(3, 14).add(12, 17).add(14, 16).add(17, 7).add(16, 5).add(7, 2).add(5, 3)
            .add(8, 10).add(9, 8).add(10, 11).add(11, 9)
            .buildMoveIndices());

        // Move #9 and #10
        addAll(new TransformationBuilder()
            .add(4, 8).add(5, 9).add(8, 12).add(9, 13).add(12, 23).add(13, 22).add(23, 4).add(22, 5)
            .add(0, 1).add(1, 3).add(2, 0).add(3, 2)
            .buildMoveIndices());

        // Move #11 and #12
        addAll(new TransformationBuilder()
            .add(6, 10).add(7, 11).add(10, 14).add(11, 15).add(14, 21).add(15, 20).add(21, 6).add(20, 7)
            .add(16, 18).add(17, 16).add(18, 19).add(19, 17)
            .buildMoveIndices());
      }
    };

    RubikCube2State loadIdentity() {
      for (int sideColor = 0; sideColor < SIDES; ++sideColor) {
        for (int cell = 0; cell < DIM * DIM; ++ cell) {
          final int cellIndex = sideColor * DIM * DIM + cell;
          state[cellIndex] = sideColor;
        }
      }
      return this;
    }

    RubikCube2State print(PrintStream ps) throws IOException {
      for (int row = 0; row < DIM; ++row) {
        for (int side = 0; side < SIDES; ++side) {
          if (side > 0) {
            ps.print("  ");
          }

          for (int col = 0; col < DIM; ++col) {
            final int cellIndex = side * DIM * DIM + row * DIM + col;
            ps.print(COLOR_CODE.charAt(state[cellIndex]));
          }
        }

        ps.print(System.lineSeparator());
      }
      return this;
    }

    int MAX_DEPTH = 1;

    RubikCube2State findSolution(PrintStream ps) throws IOException {
      final SolutionFinder finder = new SolutionFinder();
      final List<Integer> rotations = finder.find(0);
      if (rotations != null) {
        ps.println("Solution found, rotations=" + rotations);
      } else {
        ps.println("No solution found");
      }
      return this;
    }

    final class SolutionFinder {
      List<Integer> rotations = new ArrayList<>();

      List<Integer> find(int depth) {
        if (isAssembled()) {
          return new ArrayList<>(rotations);
        }

        if (depth > MAX_DEPTH) {
          return null;
        }

        final int[] newState = new int[CELLS];
        final int[] oldState = RubikCube2State.this.state;
        for (int i = 0; i < TRANSFORMATION_MOVES.size(); ++i) {
          rotateStates(state, newState, i);
          RubikCube2State.this.state = newState;
          rotations.add(i);

          final List<Integer> foundSolution = this.find(depth + 1);
          if (foundSolution != null) {
            return foundSolution;
          }

          // restore old state
          rotations.remove(rotations.size() - 1);
          RubikCube2State.this.state = oldState;
        }

        return null;
      }
    }

    RubikCube2State printIfAssembled(PrintStream ps) throws IOException {
      ps.print("Cube ");
      ps.print(isAssembled() ? "Assembled" : "Not Assembled");
      ps.println();
      return this;
    }

    boolean isAssembled() {
      final int len = SIDES - 1;

      // check all but last side
      for (int side = 0; side < len; ++side) {
        final int firstIndex = side * DIM * DIM;
        final int color = state[firstIndex];
        for (int cell = 1; cell < DIM * DIM; ++cell) {
          if (color != state[firstIndex + cell]) {
            return false;
          }
        }
      }

      return true;
    }

    RubikCube2State rotate(int rotationIndex) {
      final int[] newState = new int[CELLS];
      rotateStates(state, newState, rotationIndex);
      this.state = newState;
      return this;
    }

    static void rotateStates(int oldState[], int newState[], int rotationIndex) {
      final int[] stateIndices = TRANSFORMATION_MOVES.get(rotationIndex);
      for (int i = 0; i < CELLS; ++i) {
        newState[stateIndices[i]] = oldState[i];
      }
    }
  }
}
