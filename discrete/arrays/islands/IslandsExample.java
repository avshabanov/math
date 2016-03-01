import java.util.HashMap;
import java.util.Map;

/**
 * Sample run:
 * <pre>
 * Number of islands= 3, optNumber=3 in ocean=
 * |X    XX   |
 * |  X  X    |
 * |  X       |
 * |          |
 *
 *
 * Number of islands= 4, optNumber=4 in ocean=
 * |X  X|
 * |    |
 * |    |
 * |X  X|
 *
 *
 * Number of islands= 1, optNumber=1 in ocean=
 * |XX |
 * |X  |
 * |   |
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class IslandsExample {

  public static void main(String[] args) {
    demo(new Ocean(10, 4).set(0, 0).set(2, 1).set(2, 2).set(5, 0).set(6, 0).set(5, 1));
    demo(new Ocean(4, 4).set(0, 0).set(0, 3).set(3, 3).set(3, 0));
    demo(new Ocean(3, 3).set(0, 0).set(0, 1).set(1, 0));
  }

  public static void demo(Ocean ocean) {
    System.out.println("Number of islands= " + getNumberOfIslands(ocean) +
        ", optNumber=" + optGetNumberOfIslands(ocean) +
        " in ocean=\n" + ocean);
  }

  private static int getNumberOfIslands(Ocean ocean) {
    final IslandHolder islandHolder = new IslandHolder();

    final Islands islands = new Islands(ocean.getWidth(), ocean.getHeight());

    for (int h = 0; h < ocean.getHeight(); ++h) {
      for (int w = 0; w < ocean.getWidth(); ++w) {
        if (!ocean.get(w, h)) {
          continue; // water, continue
        }

        final Island leftIsland = (w > 0 ? islands.get(w - 1, h) : null);
        final Island topIsland = (h > 0 ? islands.get(w, h - 1) : null);

        // try unite islands
        Island curIsland;
        if (leftIsland != null && topIsland != null) {
          // unite islands
          final Integer leftId = leftIsland.holder.id;
          if (!leftId.equals(topIsland.holder.id)) {
            islandHolder.map.remove(leftId);

            // override holder, so that all the left cells will refer to the same one
            leftIsland.holder = topIsland.holder;
          }
          curIsland = topIsland;
        } else {
          curIsland = (topIsland != null ? topIsland : leftIsland);
        }

        if (curIsland == null) {
          curIsland = new Island();
          curIsland.holder = new Island.Holder(islandHolder.id++);
          islandHolder.map.put(curIsland.holder.id, curIsland);
        }

        islands.set(w, h, curIsland);
      }
    }

    return islandHolder.map.size();
  }

  private static int optGetNumberOfIslands(Ocean ocean) {
    final IslandHolder islandHolder = new IslandHolder();

    final Islands islands = new Islands(ocean.getWidth(), Math.min(2, ocean.getHeight()));

    for (int h = 0; h < ocean.getHeight(); ++h) {
      for (int w = 0; w < ocean.getWidth(); ++w) {
        if (!ocean.get(w, h)) {
          islands.set(w, h % 2, null); // reset prev island
          continue; // water, continue
        }

        final Island leftIsland = (w > 0 ? islands.get(w - 1, h % 2) : null);
        final Island topIsland = (h > 0 ? islands.get(w, (h - 1) % 2) : null);

        // try unite islands
        Island curIsland;
        if (leftIsland != null && topIsland != null) {
          // unite islands
          final Integer leftId = leftIsland.holder.id;
          if (!leftId.equals(topIsland.holder.id)) {
            islandHolder.map.remove(leftId);

            // override holder, so that all the left cells will refer to the same one
            leftIsland.holder = topIsland.holder;
          }
          curIsland = topIsland;
        } else {
          curIsland = (topIsland != null ? topIsland : leftIsland);
        }

        if (curIsland == null) {
          curIsland = new Island();
          curIsland.holder = new Island.Holder(islandHolder.id++);
          islandHolder.map.put(curIsland.holder.id, curIsland);
        }

        islands.set(w, h % 2, curIsland);
      }
    }

    return islandHolder.map.size();
  }

  //private static final class

  private static final class IslandHolder {
    int id = 0;
    Map<Integer, Island> map = new HashMap<>();
  }

  private static final class Island {
    Holder holder;

    static final class Holder {
      private final Integer id;

      public Holder(Integer id) {
        this.id = id;
      }
    }

    @Override
    public String toString() {
      return "(" + holder.id + ')';
    }
  }

  private static abstract class Field2DSupport {
    private final int width;
    private final int height;

    protected Field2DSupport(int width, int height) {
      this.width = width;
      this.height = height;
    }

    public int getWidth() {
      return width;
    }

    public int getHeight() {
      return height;
    }

    protected int getArrayOffset(int x, int y) {
      if ((x >= 0) && (x < width) && (y >= 0) && (y < height)) {
        return y * width + x;
      }

      throw new IllegalArgumentException("Coordinates are outside the bounds, x=" + x + ", y=" + y);
    }
  }

  private static final class Islands extends Field2DSupport {
    private final Island[] map;

    public Islands(int width, int height) {
      super(width, height);
      this.map = new Island[width * height];
    }

    public void set(int x, int y, Island val) {
      this.map[getArrayOffset(x, y)] = val;
    }

    public Island get(int x, int y) {
      return this.map[getArrayOffset(x, y)];
    }
  }

  /**
   * Represents an ocean and islands, water is false, island surface is true.
   */
  private static final class Ocean extends Field2DSupport {
    private final boolean[] map;

    public Ocean(int width, int height) {
      super(width, height);
      this.map = new boolean[width * height];
    }

    public Ocean set(int x, int y) {
      return set(x, y, true);
    }

    public Ocean set(int x, int y, boolean val) {
      map[getArrayOffset(x, y)] = val;
      return this;
    }

    public boolean get(int x, int y) {
      return map[getArrayOffset(x, y)];
    }

    @Override
    public String toString() {
      final StringBuilder builder = new StringBuilder();
      for (int h = 0; h < getHeight(); ++h) {
        builder.append('|');
        for (int w = 0; w < getWidth(); ++w) {
          builder.append(get(w, h) ? 'X' : ' ');
        }
        builder.append('|').append('\n');
      }
      builder.append('\n');
      return builder.toString();
    }
  }
}
