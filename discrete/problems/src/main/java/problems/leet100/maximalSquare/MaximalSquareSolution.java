package problems.leet100.maximalSquare;

/**
 * 221. Maximal square:
 * <p>Given a 2D binary matrix filled with 0's and 1's, find the largest square containing only 1's and return its area.</p>
 * Submission result:
 * <p>
 * Runtime: 4 ms, faster than 95.81% of Java online submissions for Maximal Square.
 * Memory Usage: 40.9 MB, less than 100.00% of Java online submissions for Maximal Square.
 * </p>
 */
public class MaximalSquareSolution {
  public static final class Demo1 {
    public static void main(String[] args) {
      demo(1, 1, "0");
      demo(1, 1, "1");
      demo(2, 2, "1111");
      demo(2, 2, "0000");
      demo(5, 4, "" +
          "10100" +
          "10111" +
          "11111" +
          "10010");
    }
  }

  private static void demo(int width, int heigth, String contents) {
    System.out.println("Max square area: " + maximalSquare(rectFromString(width, heigth, contents)));
  }

  private static char[][] rectFromString(int width, int heigth, String contents) {
    if (contents.length() != width * heigth) {
      throw new IllegalArgumentException("invalid contents size=" + contents.length());
    }
    final char[][] matrix = new char[heigth][];
    for (int h = 0; h < heigth; ++h) {
      matrix[h] = new char[width];
      for (int w = 0; w < width; ++w) {
        matrix[h][w] = contents.charAt(h * width + w);
      }
    }
    return matrix;
  }

  private static int maximalSquare(char[][] matrix) {
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
