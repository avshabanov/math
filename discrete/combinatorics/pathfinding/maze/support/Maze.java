package maze.support;

import java.util.BitSet;

/**
 * @author Alexander Shabanov
 */
public final class Maze {
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

  public boolean isFree(int x, int y) {
    return !bitSet.get(x + y * width);
  }

  public boolean isFree(PathNode pathNode) {
    return isFree(pathNode.getX(), pathNode.getY());
  }

  public void print() {
    System.out.println("Maze:");
    for (int y = 0; y < getHeight(); ++y) {
      for (int x = 0; x < getWidth(); ++x) {
        System.out.print(isFree(x, y) ? "0" : "1");
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
