package maze;

import maze.support.Maze;
import maze.support.PathNode;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Naïve brute-force pathfinder algorithm. Wouldn't work in real work (e.g. 2D game).
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
 * [[0,3], [0,2], [0,1], [0,0], [1,0], [2,0], [2,1]]
 * ---
 * Maze:
 * 00000
 * 01000
 * 00110
 * 00000
 * Path from=[0,3] to=[4,1]
 * [[0,3], [1,3], [2,3], [3,3], [4,3], [4,2], [4,1]]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class NaivePathfinder {

  public static void main(String[] args) {
    demo(Maze.getDemoMaze1(), new PathNode(0, 3), new PathNode(2, 1));
    demo(Maze.getDemoMaze1(), new PathNode(0, 3), new PathNode(4, 1));
  }

  static void demo(Maze maze, PathNode from, PathNode to) {
    System.out.println("---");
    maze.print();
    System.out.println("Path from=" + from + " to=" + to);
    System.out.println(getShortestPath(maze, from, to));
  }

  static List<PathNode> getShortestPath(Maze maze, PathNode from, PathNode to) {
    final List<List<PathNode>> allPaths = new ArrayList<>();
    findPathRecursive(maze, from, to, new HashSet<>(), new ArrayList<>(), allPaths);
    if (allPaths.isEmpty()) {
      throw new IllegalStateException("No path from=" + from + " to=" + to);
    }
    return allPaths.get(0);
  }

  //
  // Private
  //

  private static void findPathRecursive(Maze maze,
                                        PathNode current,
                                        PathNode to,
                                        Set<PathNode> steps,
                                        List<PathNode> currentPath,
                                        List<List<PathNode>> allPaths) {
    if (!maze.isFree(current) || steps.contains(current)) {
      return;
    }

    steps.add(current);
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
        findPathRecursive(maze, new PathNode(current.getX() - 1, current.getY()), to, steps, currentPath, allPaths);
      }
      // try right
      if (current.getX() < (maze.getWidth() - 1)) {
        findPathRecursive(maze, new PathNode(current.getX() + 1, current.getY()), to, steps, currentPath, allPaths);
      }
      // try top
      if (current.getY() > 0) {
        findPathRecursive(maze, new PathNode(current.getX(), current.getY() - 1), to, steps, currentPath, allPaths);
      }
      // try left
      if (current.getY() < (maze.getHeight() - 1)) {
        findPathRecursive(maze, new PathNode(current.getX(), current.getY() + 1), to, steps, currentPath, allPaths);
      }
    } while (false);

    steps.remove(current);
    currentPath.remove(currentPath.size() - 1);
  }
}
