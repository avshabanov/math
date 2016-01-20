package maze.support;

import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Alexander Shabanov
 */
public final class Maze {
  private static final int PRINT_SIZE_LIMIT = 30;

  private final BitSet bitSet;
  private final int width;
  private final int height;

  public Maze(int width, int height) {
    this.bitSet = new BitSet(width * height);
    this.width = width;
    this.height = height;
  }

  public int getWidth() {
    return width;
  }

  public int getHeight() {
    return height;
  }

  public Maze t(int x, int y) {
    final int bitIndex = x + y * width;
    bitSet.set(bitIndex, !bitSet.get(bitIndex));
    return this;
  }

  public int getMaxPathIndex() {
    return width * height;
  }

  public boolean isFree(int pathIndex) {
    assert pathIndex < getMaxPathIndex();
    return !bitSet.get(pathIndex);
  }

  public boolean isFree(int x, int y) {
    return isFree(x + y * width);
  }

  public boolean isFree(PathNode pathNode) {
    return isFree(pathNode.getX(), pathNode.getY());
  }

  public void print() {
    System.out.println("Maze:");
    if (getHeight() > PRINT_SIZE_LIMIT || getWidth() > PRINT_SIZE_LIMIT) {
      System.out.println("width=" + getWidth() + ", height=" + getHeight());
      return;
    }

    for (int y = 0; y < getHeight(); ++y) {
      for (int x = 0; x < getWidth(); ++x) {
        System.out.print(isFree(x, y) ? "0" : "1");
      }
      System.out.println();
    }
  }

  public void printPath(List<PathNode> path) {
    System.out.println("path=" + path);
    if (getHeight() > PRINT_SIZE_LIMIT || getWidth() > PRINT_SIZE_LIMIT) {
      return;
    }

    final Map<PathNode, Integer> pathPointIndexes = new HashMap<>(path.size() * 2);
    for (int i = 0; i < path.size(); ++i) {
      pathPointIndexes.put(path.get(i), i);
    }

    for (int y = 0; y < getHeight(); ++y) {
      for (int x = 0; x < getWidth(); ++x) {
        Integer pathPointIndex = pathPointIndexes.get(new PathNode(x, y));
        System.out.print(pathPointIndex == null ? "[XX]" : String.format(" %02d ", pathPointIndex));
      }
      System.out.println();
    }
  }

  public static Maze getDemoMaze1() {
    final Maze maze = new Maze(5, 4);
    maze.t(1, 1).t(2, 2).t(3, 2);
    return maze;
  }
}
