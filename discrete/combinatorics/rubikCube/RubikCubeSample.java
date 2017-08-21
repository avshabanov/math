import java.io.IOException;
import java.io.PrintStream;
import java.util.*;
import java.util.function.BiFunction;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * @author Alexander Shabanov
 */
public class RubikCubeSample {

  public static void main(String[] args) throws IOException {
    if (args.length > 0 && args[0].equals("0")) {
      debugRotations();
    } else if (args.length > 0 && args[0].equals("1")) {
      demo1();
    } else if (args.length > 0 && args[0].equals("2")) {
      demo2();
    } else if (args.length > 0 && args[0].equals("3")) {
      demo3();
    } else {
      demo3();
    }
  }

  static void demo3() throws IOException {
    System.out.println("RubikState #3:");
    RubikCube2State s = new RubikCube2State();
    s.setStates("YOORCYCRGYGWCGCGWRWYOROW").print(System.out);
    s.findSolution(System.out);
  }

  static void demo2() throws IOException {
    System.out.println("RubikState #2:");
    RubikCube2State s = new RubikCube2State();
    s
        .loadIdentity()
        //.rotate(0).rotate(5).rotate(5)
        //.rotate(1).rotate(5).rotate(0).rotate(9).rotate(11)
        //.rotate(1).rotate(5).rotate(7).rotate(9).rotate(11)
        .rotate(0).rotate(10).rotate(2).rotate(6).rotate(4)
        .print(System.out).printIfAssembled(System.out);

    s.findSolution(System.out);

    s.print(System.out, true);

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

  static void debugRotations() throws IOException {
    final int[] arr = new int[RubikCube2State.CELLS];
    for (int i = 0; i < arr.length; ++i) {
      arr[i] = i;
    }

    final Set<List<String>> arrs = new HashSet<>();
    for (int j = 0; j < 12; ++j) {
      final int[] newArr = new int[arr.length];
      RubikCube2State.rotateStates(arr, newArr, j);
      final List<String> arrStr = IntStream.of(newArr).mapToObj(Integer::toString).collect(Collectors.toList());
      if (!arrs.add(arrStr)) {
        throw new AssertionError("Duplicate rotation: " + j);
      }
      //System.out.println("Arr=" + arrStr);
    }
    System.out.println("OK: all rotations are unique");

    for (int j = 0; j < 6; ++j) {
      final int[] arr1 = new int[arr.length];
      final int[] arr2 = new int[arr.length];
      RubikCube2State.rotateStates(arr, arr1, j * 2);
      RubikCube2State.rotateStates(arr1, arr2, j * 2 + 1);
      if (!Arrays.equals(arr, arr2)) {
        throw new AssertionError("Non reversible rotation #" + j * 2);
      }
    }
    System.out.println("OK: all rotations are reversible");

    RubikCube2State s = new RubikCube2State();
    s.setStates("OOOOYYYYGGGGWWWWRRRRCCCC");
    RubikCube2State s2 = new RubikCube2State();
    s2.loadIdentity();
    if (!Arrays.equals(s.state, s2.state)) {
      throw new AssertionError("Unexpected identity state");
    }
    System.out.println("OK: identity state");

    s = new RubikCube2State().loadIdentity();
    final Map<Integer, Set<List<Integer>>> cubeStates = new HashMap<>();
    final Random random = new Random(1231324L);
    int stateMatches = 0;
    for (int i = 0; i < 10000; ++i) {
      final int rotationIndex = random.nextInt(RubikCube2State.SIDES * RubikCube2State.DIM);
      s.rotate(rotationIndex);

      final int cubeIndex = s.foldState();
      final Set<List<Integer>> stateSet = cubeStates.computeIfAbsent(cubeIndex, (k) -> new HashSet<>());
      final List<Integer> stateList = IntStream.of(s.state).boxed().collect(Collectors.toList());

      if (stateSet.contains(stateList)) {
        ++stateMatches;
      }

      stateSet.add(stateList);
    }
    // Approximately 10% of matches
    System.out.println("OK: rotations/state indexes verified, stateMatches=" + stateMatches);
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

  static final class VertexIndexCoordinates {
    final int index1;
    final int index2;
    final int index3;
    final int initialPosition;

    public VertexIndexCoordinates(int index1, int index2, int index3, int initialPosition) {
      this.index1 = index1;
      this.index2 = index2;
      this.index3 = index3;
      this.initialPosition = initialPosition;
    }
  }

  static final class VertexDefinitions {
    static final int VERTEX_MASK = (1 << VertexDefinitionsBuilder.CUBE_VERTEX_COUNT) - 1;

    final Map<Integer, VertexIndexCoordinates> colorToVertexIndex;
    final VertexIndexCoordinates[] vertexIndexCoordinates;

    public VertexDefinitions(Map<Integer, VertexIndexCoordinates> colorToVertexIndex) {
      this.colorToVertexIndex = new HashMap<>(colorToVertexIndex);
      this.vertexIndexCoordinates = colorToVertexIndex.values()
          .stream().sorted(Comparator.comparingInt(x -> x.initialPosition)).collect(Collectors.toList())
          .toArray(new VertexIndexCoordinates[colorToVertexIndex.size()]);
    }

    /**
     * This is the crux of this algorithm, a function, that determines a unique number corresponding to
     * the particular cube state.
     *
     * @return Cube state index
     */
    public int getCubeStateIndex(int[] cubeState) {
      assert cubeState.length == RubikCube2State.CELLS;

      int cubeStateIndex = 0;
      int mappedPositionFlags = 0;

      for (int i = 0; i < vertexIndexCoordinates.length; ++i) {
        VertexIndexCoordinates coordinates = vertexIndexCoordinates[i];
        final int color1 = cubeState[coordinates.index1] & RubikCube2State.COLOR_MASK_FLAGS;
        final int color2 = cubeState[coordinates.index2] & RubikCube2State.COLOR_MASK_FLAGS;
        final int color3 = cubeState[coordinates.index3] & RubikCube2State.COLOR_MASK_FLAGS;

        final VertexIndexCoordinates mappedCoordinate = colorToVertexIndex.get(getColorFold(color1, color2, color3));
        if (mappedCoordinate == null) {
          throw new IllegalStateException("Invalid mapped coordinate, originated for vertex index=" + i);
        }

        // TODO: remove hardcoded constant "3" from here, 2^3 == 8 which is a number of vertices initial positions
        cubeStateIndex = cubeStateIndex << 3;
        cubeStateIndex |= mappedCoordinate.initialPosition;
        mappedPositionFlags |= (1 << mappedCoordinate.initialPosition);
      }

      if (mappedPositionFlags != VERTEX_MASK) {
        throw new AssertionError("Duplicate or missing mapped position");
      }

      return cubeStateIndex;
    }

    static int getColorFold(int color1, int color2, int color3) {
      return (1 << color1) | (1 << color2) | (1 << color3);
    }
  }

  static final class VertexDefinitionsBuilder {
    static final int CUBE_VERTEX_COUNT = 8;

    final Map<Integer, VertexIndexCoordinates> colorToVertexIndex = new HashMap<>();

    // verification data structures
    final Map<Integer, Integer> colorCount = new HashMap<>();
    final BiFunction<Integer, Integer, Integer> colorCompute = (k, v) -> (v == null) ? 1 : (v + 1);

    final int[] coordinates = new int[RubikCube2State.CELLS];

    VertexDefinitionsBuilder add(int color1, int color2, int color3, VertexIndexCoordinates vertexIndex) {
      // fill out verification data structures
      colorCount.compute(color1, colorCompute);
      colorCount.compute(color2, colorCompute);
      colorCount.compute(color3, colorCompute);

      addCoordinate(vertexIndex.index1);
      addCoordinate(vertexIndex.index2);
      addCoordinate(vertexIndex.index3);

      // finally put an entry
      if (colorToVertexIndex.put(VertexDefinitions.getColorFold(color1, color2, color3), vertexIndex) != null) {
        throw new IllegalStateException("Duplicate vertex entry");
      }

      return this;
    }

    VertexDefinitions build() {
      // verify cube colors
      if (colorCount.size() != RubikCube2State.SIDES) {
        throw new IllegalStateException("Unexpected number of colors");
      }

      // verify color count per cube "node"
      for (final int value : colorCount.values()) {
        if (value != (RubikCube2State.DIM * RubikCube2State.DIM)) {
          throw new IllegalStateException("Unexpected number of color entries");
        }
      }

      // verify initial positions
      final List<Integer> initialPositions = colorToVertexIndex.values().stream()
          .map(x -> x.initialPosition).sorted().collect(Collectors.toList());
      final List<Integer> expectedInitPos = IntStream.range(0, CUBE_VERTEX_COUNT)
          .boxed().collect(Collectors.toList());
      if (!initialPositions.equals(expectedInitPos)) {
        throw new IllegalStateException("Invalid initial positions=" + initialPositions);
      }

      return new VertexDefinitions(colorToVertexIndex);
    }

    private void addCoordinate(int coordinateIndex) {
      final int oldValue = coordinates[coordinateIndex];
      if (oldValue != 0) {
        throw new IllegalStateException("Duplicate coordinate index=" + coordinateIndex);
      }

      coordinates[coordinateIndex] = 1;
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

    static final int COLOR_MASK_BITS = 3;
    static final int COLOR_MASK_FLAGS = (1 << COLOR_MASK_BITS) - 1;

    static final String COLOR_CODE = "OYGWRC";

    static final int DIM = 2;
    static final int SIDES = 6;
    static final int CELLS = SIDES * DIM * DIM;
    int state[] = new int[CELLS];

    static final VertexDefinitions VERTEX_DEFINITIONS = new VertexDefinitionsBuilder()
        .add(CL_ORANGE, CL_YELLOW, CL_CYAN, new VertexIndexCoordinates(0, 4, 22, 0))
        .add(CL_ORANGE, CL_WHITE, CL_CYAN, new VertexIndexCoordinates(1, 13, 23, 1))
        .add(CL_ORANGE, CL_YELLOW, CL_GREEN, new VertexIndexCoordinates(2, 5, 8, 2))
        .add(CL_ORANGE, CL_WHITE, CL_GREEN, new VertexIndexCoordinates(3, 9, 12, 3))
        .add(CL_RED, CL_YELLOW, CL_CYAN, new VertexIndexCoordinates(6, 18, 20, 4))
        .add(CL_RED, CL_YELLOW, CL_GREEN, new VertexIndexCoordinates(7, 10, 16, 5))

        .add(CL_RED, CL_WHITE, CL_GREEN, new VertexIndexCoordinates(11, 14, 17, 6))
        .add(CL_RED, CL_WHITE, CL_CYAN, new VertexIndexCoordinates(15, 19, 21, 7))
        .build();

    static final List<int[]> TRANSFORMATION_MOVES = new ArrayList<int[]>() {
      {
        // Move #1 and #2
        addAll(new TransformationBuilder()
            .add(0, 8).add(2, 10).add(8, 16).add(10, 18).add(16, 20).add(18, 22).add(20, 0).add(22, 2)
            .add(4, 5).add(5, 7).add(6, 4).add(7, 6)
            .buildMoveIndices());

        // Move #3 and #4
        addAll(new TransformationBuilder()
            .add(1, 9).add(3, 11).add(9, 17).add(11, 19).add(17, 21).add(19, 23).add(21, 1).add(23, 3)
            .add(12, 14).add(13, 12).add(14, 15).add(15, 13)
            .buildMoveIndices());

        // Move #5 and #6
        addAll(new TransformationBuilder()
            .add(0, 13).add(1, 15).add(13, 19).add(15, 18).add(19, 6).add(18, 4).add(6, 0).add(4, 1)
            .add(23, 21).add(22, 23).add(21, 20).add(20, 22)
            .buildMoveIndices());

        // Move #7 and #8
        addAll(new TransformationBuilder()
            .add(2, 12).add(3, 14).add(12, 17).add(14, 16).add(17, 7).add(16, 5).add(7, 2).add(5, 3)
            .add(8, 9).add(9, 11).add(10, 8).add(11, 10)
            .buildMoveIndices());

        // Move #9 and #10
        addAll(new TransformationBuilder()
            .add(4, 8).add(5, 9).add(8, 12).add(9, 13).add(12, 23).add(13, 22).add(23, 4).add(22, 5)
            .add(0, 2).add(1, 0).add(2, 3).add(3, 1)
            .buildMoveIndices());

        // Move #11 and #12
        addAll(new TransformationBuilder()
            .add(6, 10).add(7, 11).add(10, 14).add(11, 15).add(14, 21).add(15, 20).add(21, 6).add(20, 7)
            .add(16, 17).add(17, 19).add(18, 16).add(19, 18)
            .buildMoveIndices());
      }
    };

    static int charCodeToInt(char ch) {
      switch (Character.toUpperCase(ch)) {
        case 'C': return CL_CYAN;
        case 'Y': return CL_YELLOW;
        case 'O': return CL_ORANGE;
        case 'G': return CL_GREEN;
        case 'R': return CL_RED;
        case 'W': return CL_WHITE;
      }

      throw new IllegalArgumentException("Unknown character=" + ch);
    }

    int foldState() {
      return VERTEX_DEFINITIONS.getCubeStateIndex(this.state);
    }

    RubikCube2State setStates(String stateStr) {
      if (stateStr.length() != CELLS) {
        throw new IllegalArgumentException("newState");
      }

      final int[] newState = new int[CELLS];
      for (int i = 0; i < CELLS; ++i) {
        newState[i] = (i << COLOR_MASK_BITS) | charCodeToInt(stateStr.charAt(i));
      }

      this.state = newState;
      return this;
    }

    RubikCube2State loadIdentity() {
      for (int sideColor = 0, i = 0; sideColor < SIDES; ++sideColor) {
        for (int cell = 0; cell < DIM * DIM; ++cell, ++i) {
          final int cellIndex = sideColor * DIM * DIM + cell;
          state[cellIndex] = (i << COLOR_MASK_BITS) | sideColor;
        }
      }
      return this;
    }

    RubikCube2State print(PrintStream ps) throws IOException {
      return print(ps, false);
    }

    RubikCube2State print(PrintStream ps, boolean includeIndices) throws IOException {
      for (int row = 0; row < DIM; ++row) {
        for (int side = 0; side < SIDES; ++side) {
          if (side > 0) {
            ps.print("  ");
          }

          for (int col = 0; col < DIM; ++col) {
            final int cellIndex = side * DIM * DIM + row * DIM + col;
            if (includeIndices) {
              final int absoluteIndex = side * DIM * DIM + row * DIM + col;
              ps.print(String.format(" %02d:%02d-", absoluteIndex, state[cellIndex] >> COLOR_MASK_BITS));
            }
            ps.print(COLOR_CODE.charAt(state[cellIndex] & COLOR_MASK_FLAGS));
          }
        }

        ps.print(System.lineSeparator());
      }
      return this;
    }

    void findSolution(PrintStream ps) throws IOException {
      final SolutionFinder finder = new SolutionFinder();
      long timeDelta = System.currentTimeMillis();
      finder.find(0);
      timeDelta = System.currentTimeMillis() - timeDelta;
      final List<Integer> solution = finder.solution;
      if (solution != null) {
        ps.println("Solution found, rotations solution=" + solution);
      } else {
        ps.println("No solution found");
      }
      ps.println("\tIterations=" + finder.iterations + ", timeSpent=" + timeDelta + " msec");
    }

    final class SolutionFinder {
      static final int MAX_DEPTH = 20;

      // this is to enable optimization: avoid reallocating array on each depth state and to
      // enable heuristics which is to match current state with the previous one to prune
      // solution candidate chains resulting in the same state as we had before
      final int[][] depthStates = new int[MAX_DEPTH][CELLS];
      final int[] depthStateHashCodes = new int[MAX_DEPTH];

      final Set<Integer> visitedStates = new HashSet<>(80000);

      // iterations count, for statistics purposes
      long iterations = 0;

      List<Integer> rotations = new ArrayList<>();
      List<Integer> solution = null;

      void find(int depth) {
        ++iterations;
        if (iterations % 1000000000L == 0) {
          System.out.println(new Date() + " - Iterations so far: " +
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 iterations + ", solution=" + solution + ", current rotations=" + rotations);
        }

        if (isAssembled()) {
          if (solution == null || rotations.size() < solution.size()) {
            solution = new ArrayList<>(rotations);
          }
          return;
        }

        if (depth >= MAX_DEPTH || (solution != null && depth > solution.size())) {
          return;
        }

        // TODO: remove if you need optimal solution
        final int cubeStateIndex = RubikCube2State.this.foldState();
        if (visitedStates.contains(cubeStateIndex)) {
          // this combination of vertices already met, discard this branch
          return;
        }
        visitedStates.add(cubeStateIndex);

        final int[] newState = this.depthStates[depth];
        final int[] oldState = RubikCube2State.this.state;
        for (int i = 0; i < TRANSFORMATION_MOVES.size(); ++i) {
          rotateStates(state, newState, i);

          // heuristic: discontinue search if there is a previous match
          final int newStateHashCode = Arrays.hashCode(newState);
          boolean matches = false;
          for (int j = 0; j < depth; ++j) {
            if (depthStateHashCodes[j] == newStateHashCode && Arrays.equals(newState, depthStates[j])) {
              matches = true;
              break;
            }
          }

          if (matches) {
            continue; // helps reduce iterations from 5E10^6 to 3E10^6
          }

          depthStateHashCodes[depth] = newStateHashCode;
          RubikCube2State.this.state = newState;
          rotations.add(i);

          this.find(depth + 1);

          // restore old state
          rotations.remove(rotations.size() - 1);
          RubikCube2State.this.state = oldState;
        }
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
        final int color = state[firstIndex] & COLOR_MASK_FLAGS;
        for (int cell = 1; cell < DIM * DIM; ++cell) {
          if (color != (state[firstIndex + cell] & COLOR_MASK_FLAGS)) {
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
