package problems.leet100.challenge528.w3;

import java.util.HashMap;
import java.util.Map;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/530/week-3/3302/
 * <p>Given a 2d grid map of '1's (land) and '0's (water), count the number of islands. An island is surrounded by
 * water and is formed by connecting adjacent lands horizontally or vertically. You may assume all four edges of the
 * grid are all surrounded by water.</p>
 */
public final class NumberOfIslandsSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      char[][] grid = {
          "11000".toCharArray(),
          "11000".toCharArray(),
          "00100".toCharArray(),
          "00011".toCharArray(),
      };
      System.out.printf("Num islands: %d\n", numIslands(grid));
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      char[][] grid = {
          "11110".toCharArray(),
          "11010".toCharArray(),
          "11000".toCharArray(),
          "00000".toCharArray(),
      };
      System.out.printf("Num islands: %d\n", numIslands(grid));
    }
  }

  private static int numIslands(char[][] grid) {
    final IslandMap map = new IslandMap(grid);
    for (int w = 0; w < grid.length; ++w) {
      final int hLen = grid[w].length;
      for (int h = 0; h < hLen; ++h) {
        map.visitIsland(null, w, h);
      }
    }
    return map.islandIndex;
  }

  private static final class IslandMap {
    private int islandIndex = 0;
    final char[][] grid;
    private Map<IntPair, Integer> islands = new HashMap<>();

    public IslandMap(char[][] grid) {
      this.grid = grid;
    }

    void visitIsland(Integer connectTo, int w, int h) {
      char ch = grid[w][h];
      if (ch == '0') {
        return;
      }

      final IntPair pair = new IntPair(w, h);
      Integer existing = islands.get(pair);
      if (existing != null) {
        // this cell has been visited already, skip it
        if (connectTo != null && !connectTo.equals(existing)) {
          throw new IllegalStateException();
        }
        return;
      }

      // mark this island as visited
      if (connectTo == null) {
        connectTo = ++islandIndex;
      }
      existing = connectTo;

      islands.put(pair, existing);

      if (h > 0) {
        visitIsland(existing, w, h - 1);
      }
      if (w > 0) {
        visitIsland(existing, w - 1, h);
      }
      if ((h + 1) < grid[w].length) {
        visitIsland(existing, w, h + 1);
      }
      if ((w + 1) < grid.length) {
        visitIsland(existing, w + 1, h);
      }
    }
  }

  private static final class IntPair {
    final int a;
    final int b;

    IntPair(int a, int b) {
      this.a = a;
      this.b = b;
    }

    @Override public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof IntPair)) return false;
      final IntPair intPair = (IntPair) o;
      if (a != intPair.a) return false;
      return b == intPair.b;
    }
    @Override public int hashCode() { return 31 * a + b; }
    @Override public String toString() { return "{" + a + ", " + b + '}'; }
  }
}
