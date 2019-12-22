package problems.leet100.maximalRectangle;

/**
 * 85. Maximal Rectangle
 * https://leetcode.com/problems/maximal-rectangle/
 * <p>
 * Given a 2D binary matrix filled with 0's and 1's, find the largest rectangle containing only 1's and return its area.
 * </p>
 * TODO: optimize recursion calls, make better use of memory by not instantiating solution finder multiple times,
 *  get rid of dimensions class (inline width and height)
 * <p>
 * Runtime: 1289 ms, faster than 5.10% of Java online submissions for Maximal Rectangle.
 * Memory Usage: 45.1 MB, less than 19.57% of Java online submissions for Maximal Rectangle.
 * </p>
 */
public class MaximalRectangleSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(2, 2, "1111");

      demo(1, 1, "0");
      demo(1, 1, "1");

      demo(2, 2, "0000");
      demo(5, 4, "" +
          "10100" +
          "10111" +
          "11111" +
          "10010");
    }
  }

  private static void demo(int width, int heigth, String contents) {
    System.out.println("Max rect area: " + maximalRectangle(rectFromString(width, heigth, contents)));
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

  private static int maximalRectangle(char[][] matrix) {
    final int height = matrix.length;
    if (height == 0) {
      return 0;
    }

    final int width = matrix[0].length;
    if (width == 0) {
      return 0;
    }

    Dimensions maxDimensions = Dimensions.ZERO;
    for (int h = 0; h < height; ++h) {
      final int verticalLengthLimit = height - h;
      for (int w = 0; w < width; ++w) {
        final int horizontalLengthLimit = width - w;
        final Dimensions limitDimensions = new Dimensions(horizontalLengthLimit, verticalLengthLimit);
        if (maxDimensions.area() > limitDimensions.area()) {
          // skip processing, if it is obvious, that remaining area won't fit the bigger rectangle
          break;
        }

        final Dimensions dimensions = maxRectFromCell(matrix, w, h, limitDimensions);
        maxDimensions = dimensions.isAreaGreaterThan(maxDimensions) ? dimensions : maxDimensions;
      }
    }

    return maxDimensions.area();
  }

  private static final class Dimensions {
    static final Dimensions ZERO = new Dimensions(0, 0);
    static final Dimensions ONE = new Dimensions(1, 1);

    final int width;
    final int height;

    Dimensions(int width, int height) {
      this.width = width;
      this.height = height;
    }

    boolean isAreaGreaterThan(Dimensions other) {
      return area() > other.area();
    }

    int area() {
      return width * height;
    }
  }

  private static Dimensions maxRectFromCell(char[][] matrix, int w, int h, Dimensions limitDimensions) {
    if (matrix[h][w] != '1') {
      return Dimensions.ZERO;
    }

    final MaxRectFinder rectFinder = new MaxRectFinder(matrix, w, h, limitDimensions);
    rectFinder.tryGrowWidth(2, 1);
    rectFinder.tryGrowHeight(1, 2);

    return rectFinder.maxFound;
  }

  private static final class MaxRectFinder {
    final char[][] matrix;
    final int x;
    final int y;
    final Dimensions limitDimensions;
    Dimensions maxFound = Dimensions.ONE;

    MaxRectFinder(char[][] matrix, int x, int y, Dimensions limitDimensions) {
      this.matrix = matrix;
      this.x = x;
      this.y = y;
      this.limitDimensions = limitDimensions;
    }

    void tryGrowHeight(int currentWidth, int newHeigth) {
      if (newHeigth > limitDimensions.height) {
        return;
      }
      for (int w = 0; w < currentWidth; ++w) {
        if (matrix[y + newHeigth - 1][x + w] != '1') {
          return;
        }
      }

      final Dimensions newDimension = new Dimensions(currentWidth, newHeigth);
      maxFound = newDimension.isAreaGreaterThan(maxFound) ? newDimension : maxFound;

      tryGrowWidth(currentWidth + 1, newHeigth);
      tryGrowHeight(currentWidth, newHeigth + 1);
    }

    void tryGrowWidth(int newWidth, int currentHeigth) {
      if (newWidth > limitDimensions.width) {
        return;
      }
      for (int h = 0; h < currentHeigth; ++h) {
        if (matrix[y + h][x + newWidth - 1] != '1') {
          return;
        }
      }

      final Dimensions newDimension = new Dimensions(newWidth, currentHeigth);
      maxFound = newDimension.isAreaGreaterThan(maxFound) ? newDimension : maxFound;

      tryGrowWidth(newWidth + 1, currentHeigth);
      tryGrowHeight(newWidth, currentHeigth + 1);
    }
  }
}
