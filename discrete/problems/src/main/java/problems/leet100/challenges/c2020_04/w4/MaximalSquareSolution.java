package problems.leet100.challenges.c2020_04.w4;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/531/week-4/3312/
 * <p>Given a 2D binary matrix filled with 0's and 1's, find the largest square containing only 1's and
 * return its area.</p>
 */
public class MaximalSquareSolution {


  // existing solution
  private static final class Leaked {
    public int maximalSquare(char[][] matrix) {
      final int height = matrix.length;
      if (height == 0) {
        return 0;
      }

      final int width = matrix[0].length;
      if (width == 0) {
        return 0;
      }

      int maxLength = 0;
      for (int h = 0; h < height; ++h) {
        final int verticalLengthLimit = height - h;
        if (maxLength >= verticalLengthLimit) {
          // skip processing, if it is obvious, that remaining area won't fit the bigger square
          break;
        }
        for (int w = 0; w < width; ++w) {
          final int lengthLimit = Math.min(verticalLengthLimit, width - w);
          if (maxLength >= lengthLimit) {
            // skip processing, if it is obvious, that remaining area won't fit the bigger square
            continue;
          }

          final int newMaxLength = maxSquareFromCell(matrix, w, h, lengthLimit);
          maxLength = Math.max(maxLength, newMaxLength);
        }
      }

      return maxLength * maxLength;
    }

    private static int maxSquareFromCell(char[][] matrix, int w, int h, int lengthLimit) {
      if (matrix[h][w] != '1') {
        return 0;
      }

      int length = 1;
      for (int newLength = length + 1; newLength <= lengthLimit; ++newLength) {
        // check, that new vertical and horizontal lines fit the length
        for (int sqh = 0; sqh < newLength; ++sqh) {
          if (matrix[h + sqh][w + length] != '1') {
            return length;
          }
          if (sqh == length) {
            // last line should also be all ones
            for (int i = 0; i < length; ++i) {
              if (matrix[h + length][w + i] != '1') {
                return length;
              }
            }
          }
        }
        length = newLength;
      }

      return length;
    }
  }
}
