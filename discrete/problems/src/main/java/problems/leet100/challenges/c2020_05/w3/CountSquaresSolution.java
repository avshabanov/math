package problems.leet100.challenges.c2020_05.w3;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/536/week-3-may-15th-may-21st/3336/
 * <p>Given a m * n matrix of ones and zeros, return how many square submatrices have all ones.</p>
 */
public class CountSquaresSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println(countSquares(new int[][] {
          {0,1,1,1},
          {1,1,1,1},
          {0,1,1,1}
      }));
    }
  }

  private static int countSquares(int[][] matrix) {
    if (matrix == null || matrix.length == 0) {
      return 0;
    }
    int result = 0;
    for (int y = 0; y < matrix.length; ++y) {
      for (int x = 0; x < matrix[0].length; ++x) {
        result += countSquaresFromPos(matrix, y, x);
      }
    }
    return result;
  }

  private static int countSquaresFromPos(int[][] matrix, int y, int x) {
    if (matrix[y][x] != 1) {
      return 0;
    }

    int result = 1; // single square of size 1
    final int dimBound = Math.min(matrix.length - y, matrix[y].length - x);
    for (int dim = 1; dim < dimBound; ++dim) {
      int xRight = x + dim;
      int yBottom = y + dim;

      // check bottom slice
      for (int i = x; i <= xRight; ++i) {
        if (matrix[yBottom][i] != 1) {
          return result;
        }
      }

      // check right slice excluding bottom-right point
      for (int i = y; i < yBottom; ++i) {
        if (matrix[i][xRight] != 1) {
          return result;
        }
      }

      ++result; // one more square found
    }

    return result;
  }
}
