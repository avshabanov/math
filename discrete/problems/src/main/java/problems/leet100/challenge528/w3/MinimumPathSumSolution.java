package problems.leet100.challenge528.w3;

import java.util.Arrays;
import java.util.stream.IntStream;

/**
 * https://leetcode.com/explore/challenge/card/30-day-leetcoding-challenge/530/week-3/3303/
 *
 * <p>Given a m x n grid filled with non-negative numbers, find a path from top left to bottom right which minimizes
 * the sum of all numbers along its path.
 * Note: You can only move either down or right at any point in time.</p>
 */
public class MinimumPathSumSolution {

  public static void main(String[] args) {
    final int[][] grid = {
        {1,3,1},
        {1,5,1},
        {4,2,1}
    };

    System.out.printf("maxPathSum=%d\n", Greedy.minPathSum(grid));
  }

  private static final class Greedy {
    private static int minPathSum(int[][] grid) {
      final int height = grid.length;
      final int width = height > 0 ? grid[0].length : 0;
      if (width == 0) {
        return 0;
      }
      if (height == 1) {
        return IntStream.of(grid[0]).sum(); // simple case
      }

      int[] slice = new int[width];
      for (int w = 0; w < width; ++w) {
        slice[w] = (w > 0 ? slice[w - 1] : 0) + grid[0][w];
      }

      int[] newSlice = new int[width];
      for (int h = 1; h < height; ++h) {
        // for each slice "downstream" we need to pick up the minimum possible path to reach out to it
        final int[] gridStride = grid[h];
        Arrays.fill(newSlice, Integer.MAX_VALUE);
        for (int i = 0; i < width; ++i) {
          for (int j = i; j < width; ++j) {
            int newSum = slice[i];
            for (int k = i; k <= j; ++k) {
              newSum += gridStride[k];
            }
            newSlice[j] = Math.min(newSlice[j], newSum);
          }
        }

        // swap slices
        int[] tmp = slice;
        slice = newSlice;
        newSlice = tmp;
      }

      return slice[width - 1];
    }
  }

  private static final class BruteForce {
    private static int minPathSum(int[][] grid) {
      final Solver s = new Solver(grid);
      s.findMaxPath(0, 0, 0);
      return s.minPath;
    }

    private static final class Solver {
      final int[][] grid;
      int minPath = Integer.MAX_VALUE;

      Solver(int[][] grid) {
        this.grid = grid;
      }

      void findMaxPath(int path, int h, int w) {
        if (h == (grid.length - 1)) {
          // special case: last horizontal
          for (int i = w; i < grid[h].length; ++i) {
            path += grid[h][i];
          }
          minPath = Math.min(path, minPath);
          return;
        }

        // intermediary case: non-last horizontal
        final int width = grid[h].length;
        for (; w < width; ++w) {
          path += grid[h][w];
          findMaxPath(path, h + 1, w);
        }
      }
    }
  }
}
