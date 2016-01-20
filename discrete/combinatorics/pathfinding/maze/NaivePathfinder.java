package maze;

import maze.support.Maze;
import maze.support.PathNode;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Naïve brute-force pathfinder algorithm. Wouldn't work efficiently in real word (e.g. 2D game).
 *
 * Sample run:
 * <pre>
 * ---
 * Maze:
 * 00000
 * 01000
 * 00110
 * 00000
 * Path from=[0,3] to=[2,1]
 * path=[[0,3], [0,2], [0,1], [0,0], [1,0], [2,0], [2,1]]
 *  03  04  05 [XX][XX]
 *  02 [XX] 06 [XX][XX]
 *  01 [XX][XX][XX][XX]
 *  00 [XX][XX][XX][XX]
 * ---
 * Maze:
 * 00000
 * 01000
 * 00110
 * 00000
 * Path from=[0,3] to=[4,1]
 * path=[[0,3], [1,3], [2,3], [3,3], [4,3], [4,2], [4,1]]
 * [XX][XX][XX][XX][XX]
 * [XX][XX][XX][XX] 06
 * [XX][XX][XX][XX] 05
 *  00  01  02  03  04
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class NaivePathfinder {

  public static void main(String[] args) {
    demo(Maze.getDemoMaze1(), new PathNode(0, 0), new PathNode(4, 3));
    demo(Maze.getDemoMaze1(), new PathNode(0, 3), new PathNode(2, 1));
    demo(Maze.getDemoMaze1(), new PathNode(0, 3), new PathNode(4, 1));

    final Maze emptyMaze = new Maze(5, 7);
    demo(emptyMaze, new PathNode(0, 0), new PathNode(4, 6));
  }

  static void demo(Maze maze, PathNode from, PathNode to) {
    System.out.println("---");
    maze.print();
    System.out.println("Path from=" + from + " to=" + to);
    maze.printPath(getShortestPath(maze, from, to));
  }

  static List<PathNode> getShortestPath(Maze maze, PathNode from, PathNode to) {
    final Solver solver = new Solver(maze, to);
    final long start = System.nanoTime();
    try {
      solver.visit(from, 0);
      if (solver.allPaths.isEmpty()) {
        throw new IllegalStateException("No path from=" + from + " to=" + to);
      }
      return solver.allPaths.get(0);
    } finally {
      final long delta = System.nanoTime() - start;
      System.out.println("Statistics: steps=" + solver.steps + ", maxDepth=" + solver.maxDepth +
          ", timeToSolve=" + delta + "ns");
    }
  }

  //
  // Private
  //

  private static final class Solver {
    private final Maze maze;
    private final PathNode to;
    private final Set<PathNode> visitedNodes = new HashSet<>();
    private final List<List<PathNode>> allPaths = new ArrayList<>();
    private final List<PathNode> currentPath = new ArrayList<>();

    // statistics
    private int steps;
    private int maxDepth;

    public Solver(Maze maze, PathNode to) {
      this.maze = maze;
      this.to = to;
    }

    void visit(PathNode current, int depth) {
      // update statistics
      ++steps;
      maxDepth = Math.max(depth, maxDepth);

      if (!maze.isFree(current) || visitedNodes.contains(current)) {
        return;
      }

      visitedNodes.add(current);
      currentPath.add(current);

      do {
        // path found?
        if (to.equals(current)) {
          if (allPaths.isEmpty() || allPaths.get(0).size() > currentPath.size()) {
            allPaths.clear();
            allPaths.add(new ArrayList<>(currentPath));
          }
          break;
        }

        // try left
        if (current.getX() > 0) {
          visit(new PathNode(current.getX() - 1, current.getY()), depth + 1);
        }
        // try right
        if (current.getX() < (maze.getWidth() - 1)) {
          visit(new PathNode(current.getX() + 1, current.getY()), depth + 1);
        }
        // try top
        if (current.getY() > 0) {
          visit(new PathNode(current.getX(), current.getY() - 1), depth + 1);
        }
        // try down
        if (current.getY() < (maze.getHeight() - 1)) {
          visit(new PathNode(current.getX(), current.getY() + 1), depth + 1);
        }
      } while (false);

      visitedNodes.remove(current);
      currentPath.remove(currentPath.size() - 1);
    }
  }


}
