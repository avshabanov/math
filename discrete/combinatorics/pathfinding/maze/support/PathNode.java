package maze.support;

/**
 * Element of path in certain maze.
 * See {@link Maze}.
 *
 * @author Alexander Shabanov
 */
public final class PathNode {
  private final int x;
  private final int y;

  public PathNode(int x, int y) {
    this.x = x;
    this.y = y;
  }

  public int getX() {
    return x;
  }

  public int getY() {
    return y;
  }

  public int getIndex(Maze maze) {
    return getX() + getY() * maze.getWidth();
  }

  public static int xFromIndex(Maze maze, int index) {
    return index % maze.getWidth();
  }

  public static int yFromIndex(Maze maze, int index) {
    return index / maze.getWidth();
  }

  public static PathNode fromIndex(Maze maze, int index) {
    return new PathNode(xFromIndex(maze, index), yFromIndex(maze, index));
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof PathNode)) return false;

    final PathNode pathNode = (PathNode) o;

    return x == pathNode.x && y == pathNode.y;

  }

  @Override
  public int hashCode() {
    int result = x;
    result = 31 * result + y;
    return result;
  }

  @Override
  public String toString() {
    return "[" + getX() + ',' + getY() + ']';
  }
}
