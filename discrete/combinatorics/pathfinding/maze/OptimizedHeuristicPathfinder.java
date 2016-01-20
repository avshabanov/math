package maze;

import maze.support.Maze;
import maze.support.PathNode;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;

/**
 * Optimized recursive search pathfinder for maze as defined in {@link maze.support.Maze} with some path finding
 * heuristics.
 *
 * @author Alexander Shabanov
 */
public final class OptimizedHeuristicPathfinder {

  public static void main(String[] args) {
    runDemo(Heuristic.NONE);
    runDemo(Heuristic.GUESS_DIRECTION);
  }

  static void runDemo(Heuristic heuristic) {
    demo(Maze.getDemoMaze1(), new PathNode(0, 0), new PathNode(4, 3), heuristic);
    demo(Maze.getDemoMaze1(), new PathNode(0, 3), new PathNode(2, 1), heuristic);
    demo(Maze.getDemoMaze1(), new PathNode(0, 3), new PathNode(4, 1), heuristic);

    final Maze emptyMaze = new Maze(5, 7);
    demo(emptyMaze, new PathNode(0, 0), new PathNode(4, 6), heuristic);

    final Maze largeEmptyMaze = new Maze(8, 9);
    demo(largeEmptyMaze, new PathNode(0, 0), new PathNode(7, 8), heuristic);
  }

  static void demo(Maze maze, PathNode from, PathNode to, Heuristic heuristic) {
    System.out.println("---");
    maze.print();
    System.out.println("Path from=" + from + " to=" + to);
    maze.printPath(getShortestPath(maze, from, to, heuristic));
  }

  public static List<PathNode> getShortestPath(Maze maze, PathNode from, PathNode to, Heuristic heuristic) {
    final Solver solver = new Solver(maze, to, heuristic);
    final long start = System.nanoTime();
    try {
      solver.visit(from.getIndex(maze), 0);
      if (solver.foundPathIndexes != null) {
        final List<PathNode> result = new ArrayList<>(solver.foundPathIndexes.length);
        for (int i = 0; i < solver.foundPathIndexes.length; ++i) {
          final int index = solver.foundPathIndexes[i];
          result.add(PathNode.fromIndex(maze, index));
        }
        return result;
      }

      throw new IllegalStateException("There is no path from=" + from + " to=" + to + " in the given maze");
    } finally {
      final long delta = System.nanoTime() - start;
      System.out.println("Statistics: steps=" + solver.steps + ", maxDepth=" + solver.maxDepth +
          ", heuristic=" + heuristic +
          ", timeToSolve=" + delta + "ns");
    }
  }

  //
  // Private
  //

  private enum Heuristic {
    NONE,
    GUESS_DIRECTION
  }

  private static final class Solver {
    final Maze maze;
    final BitSet visitorMarks;
    final int toIndex;
    final PathNode to;
    final GrowableIntArray cellIndexes;
    int[] foundPathIndexes;

    // heuristics
    private final Heuristic heuristic;

    // statistics
    int steps;
    int maxDepth;

    public Solver(Maze maze, PathNode to, Heuristic heuristic) {
      this.maze = maze; // can be reused in STA
      this.visitorMarks = new BitSet(maze.getWidth() * maze.getHeight()); // can be reused in STA
      this.to = to;
      this.toIndex = to.getIndex(maze);
      this.cellIndexes = new GrowableIntArray(maze.getWidth() * maze.getHeight()); // can be reused in STA
      this.heuristic = heuristic;
    }

    void visit(final int visitorIndex, final int depth) {
      // update statistics
      ++steps;
      maxDepth = Math.max(depth, maxDepth);

      //final int visitorIndex = current.getY() * maze.getWidth() + current.getX();
      if (!maze.isFree(visitorIndex)) {
        return; // don't try this cell if it is not free
      }

      if (foundPathIndexes != null && foundPathIndexes.length < (cellIndexes.size() + 1)) {
        return; // don't search further if more optimal path has been found
      }

      if (visitorMarks.get(visitorIndex)) {
        return; // don't try the cell that has already been visited
      }

      // mark this cell as visited and add it to the path
      visitorMarks.set(visitorIndex);
      cellIndexes.add(visitorIndex);

      if (toIndex == visitorIndex) {
        foundPathIndexes = cellIndexes.copy(); // optimal path has been found, add it to the indexes
      } else {
        switch (heuristic) {
          case NONE:
            visitNearbyCellsNoHeuristic(visitorIndex, depth);
            break;
          case GUESS_DIRECTION:
            visitCellsTowardTarget(visitorIndex, depth);
            break;
          default:
            throw new UnsupportedOperationException("Unsupported heuristic=" + heuristic);
        }
      }

      // unmark this cell as visited and remove it from the path
      cellIndexes.removeLast();
      visitorMarks.clear(visitorIndex);
    }

    private void visitNearbyCellsNoHeuristic(final int visitorIndex, final int depth) {
      if (visitorIndex >= maze.getWidth()) {
        visit(visitorIndex - maze.getWidth(), depth + 1); // visit top cell
      }
      final int bottomVisitorIndex = visitorIndex + maze.getWidth();
      if (bottomVisitorIndex < maze.getMaxPathIndex()) {
        visit(bottomVisitorIndex, depth + 1); // visit bottom cell
      }
      // try left and right cells
      final int x = visitorIndex % maze.getWidth();
      if (x > 0) {
        visit(visitorIndex - 1, depth + 1); // visit left cell
      }
      if ((x + 1) < maze.getWidth()) {
        visit(visitorIndex + 1, depth + 1); // visit right cell
      }
    }

    private void visitCellsTowardTarget(final int visitorIndex, final int depth) {
      final int x = PathNode.xFromIndex(maze, visitorIndex);
      final int y = PathNode.yFromIndex(maze, visitorIndex);

      final int dx = to.getX() - x;
      final int dy = to.getY() - y;

      if (dy > 0) {
        if (dx > 0) {
          // first quarter: dx > 0 && dy > 0
          if (dx > dy) {
            // go RIGHT first, then DOWN, LEFT, UP
            visitRightDownLeftUp(x, visitorIndex, depth);
          } else {
            // go DOWN first, then RIGHT, LEFT, UP
            visitDownRightLeftUp(x, visitorIndex, depth);
          }
        } else {
          // second quarter: dx < 0 && dy > 0
          if ((-dx) > dy) {
            // go LEFT first, then DOWN, RIGHT, UP
            visitLeftDownRightUp(x, visitorIndex, depth);
          } else {
            // go DOWN first, then LEFT, RIGHT, UP
            visitDownLeftRightUp(x, visitorIndex, depth);
          }
        }
      } else {
        if (dx < 0) {
          // third quarter: dx < 0 && dy < 0
          if (dx < dy /* both are negative, hence less */) {
            // go LEFT first, then UP, RIGHT, DOWN
            visitLeftUpRightDown(x, visitorIndex, depth);
          } else {
            // go UP first, then LEFT, RIGHT, DOWN
            visitUpLeftRightDown(x, visitorIndex, depth);
          }
        } else {
          // fourth quarter: dx > 0 && dy < 0
          if (dx > (-dy)) {
            // go RIGHT first, then UP, LEFT, DOWN
            visitRightUpLeftDown(x, visitorIndex, depth);
          } else {
            // go UP first, then RIGHT, LEFT, DOWN
            visitUpRightLeftDown(x, visitorIndex, depth);
          }
        }
      }
    }

    private void visitRightDownLeftUp(final int x, final int visitorIndex, final int depth) {
      if ((x + 1) < maze.getWidth()) { // RIGHT
        visit(visitorIndex + 1, depth + 1);
      }

      final int bottomVisitorIndex = visitorIndex + maze.getWidth();
      if (bottomVisitorIndex < maze.getMaxPathIndex()) { // DOWN
        visit(bottomVisitorIndex, depth + 1); // visit bottom cell
      }

      if (x > 0) { // LEFT
        visit(visitorIndex - 1, depth + 1);
      }

      if (visitorIndex >= maze.getWidth()) { // UP
        visit(visitorIndex - maze.getWidth(), depth + 1);
      }
    }

    private void visitLeftDownRightUp(final int x, final int visitorIndex, final int depth) {
      if (x > 0) { // LEFT
        visit(visitorIndex - 1, depth + 1);
      }

      final int bottomVisitorIndex = visitorIndex + maze.getWidth();
      if (bottomVisitorIndex < maze.getMaxPathIndex()) { // DOWN
        visit(bottomVisitorIndex, depth + 1); // visit bottom cell
      }

      if ((x + 1) < maze.getWidth()) { // RIGHT
        visit(visitorIndex + 1, depth + 1);
      }

      if (visitorIndex >= maze.getWidth()) { // UP
        visit(visitorIndex - maze.getWidth(), depth + 1);
      }
    }

    private void visitDownRightLeftUp(final int x, final int visitorIndex, final int depth) {
      final int bottomVisitorIndex = visitorIndex + maze.getWidth();
      if (bottomVisitorIndex < maze.getMaxPathIndex()) { // DOWN
        visit(bottomVisitorIndex, depth + 1); // visit bottom cell
      }

      if ((x + 1) < maze.getWidth()) { // RIGHT
        visit(visitorIndex + 1, depth + 1);
      }

      if (x > 0) { // LEFT
        visit(visitorIndex - 1, depth + 1);
      }

      if (visitorIndex >= maze.getWidth()) { // UP
        visit(visitorIndex - maze.getWidth(), depth + 1);
      }
    }

    private void visitLeftUpRightDown(final int x, final int visitorIndex, final int depth) {
      if (x > 0) { // LEFT
        visit(visitorIndex - 1, depth + 1);
      }

      if (visitorIndex >= maze.getWidth()) { // UP
        visit(visitorIndex - maze.getWidth(), depth + 1);
      }

      if ((x + 1) < maze.getWidth()) { // RIGHT
        visit(visitorIndex + 1, depth + 1);
      }

      final int bottomVisitorIndex = visitorIndex + maze.getWidth();
      if (bottomVisitorIndex < maze.getMaxPathIndex()) { // DOWN
        visit(bottomVisitorIndex, depth + 1); // visit bottom cell
      }
    }

    private void visitDownLeftRightUp(final int x, final int visitorIndex, final int depth) {
      final int bottomVisitorIndex = visitorIndex + maze.getWidth();
      if (bottomVisitorIndex < maze.getMaxPathIndex()) { // DOWN
        visit(bottomVisitorIndex, depth + 1); // visit bottom cell
      }

      if (x > 0) { // LEFT
        visit(visitorIndex - 1, depth + 1);
      }

      if ((x + 1) < maze.getWidth()) { // RIGHT
        visit(visitorIndex + 1, depth + 1);
      }

      if (visitorIndex >= maze.getWidth()) { // UP
        visit(visitorIndex - maze.getWidth(), depth + 1);
      }
    }

    private void visitUpLeftRightDown(final int x, final int visitorIndex, final int depth) {
      if (visitorIndex >= maze.getWidth()) { // UP
        visit(visitorIndex - maze.getWidth(), depth + 1);
      }

      if (x > 0) { // LEFT
        visit(visitorIndex - 1, depth + 1);
      }

      if ((x + 1) < maze.getWidth()) { // RIGHT
        visit(visitorIndex + 1, depth + 1);
      }

      final int bottomVisitorIndex = visitorIndex + maze.getWidth();
      if (bottomVisitorIndex < maze.getMaxPathIndex()) { // DOWN
        visit(bottomVisitorIndex, depth + 1); // visit bottom cell
      }
    }

    private void visitRightUpLeftDown(final int x, final int visitorIndex, final int depth) {
      if ((x + 1) < maze.getWidth()) { // RIGHT
        visit(visitorIndex + 1, depth + 1);
      }

      if (visitorIndex >= maze.getWidth()) { // UP
        visit(visitorIndex - maze.getWidth(), depth + 1);
      }

      if (x > 0) { // LEFT
        visit(visitorIndex - 1, depth + 1);
      }

      final int bottomVisitorIndex = visitorIndex + maze.getWidth();
      if (bottomVisitorIndex < maze.getMaxPathIndex()) { // DOWN
        visit(bottomVisitorIndex, depth + 1); // visit bottom cell
      }
    }

    private void visitUpRightLeftDown(final int x, final int visitorIndex, final int depth) {
      if (visitorIndex >= maze.getWidth()) { // UP
        visit(visitorIndex - maze.getWidth(), depth + 1);
      }

      if ((x + 1) < maze.getWidth()) { // RIGHT
        visit(visitorIndex + 1, depth + 1);
      }

      if (x > 0) { // LEFT
        visit(visitorIndex - 1, depth + 1);
      }

      final int bottomVisitorIndex = visitorIndex + maze.getWidth();
      if (bottomVisitorIndex < maze.getMaxPathIndex()) { // DOWN
        visit(bottomVisitorIndex, depth + 1); // visit bottom cell
      }
    }
  }

  /**
   * Memory-optimized collection for integers.
   */
  private static final class GrowableIntArray {
    private int[] arr;
    private int size;

    public GrowableIntArray(int capacity) {
      this.arr = new int[capacity];
    }

    public int size() {
      return size;
    }

    public void add(int value) {
      if (size() >= arr.length) {
        this.arr = Arrays.copyOf(this.arr, this.arr.length * 2);
      }

      this.arr[this.size] = value;
      ++this.size;
    }

    public void removeLast() {
      --this.size;
      assert this.size >= 0;
    }

    public int[] copy() {
      return Arrays.copyOfRange(this.arr, 0, size());
    }

    @Override
    public String toString() {
      final StringBuilder builder = new StringBuilder(4 + size() * 5);
      builder.append('[');
      for (int i = 0; i < size; ++i) {
        if (i > 0) {
          builder.append(',').append(' ');
        }
        builder.append(arr[i]);
      }
      builder.append(']');
      return builder.toString();
    }
  }
}
