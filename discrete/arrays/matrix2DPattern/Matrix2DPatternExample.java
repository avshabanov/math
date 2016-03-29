import support.Matrix2DSupport;

import java.util.ArrayList;
import java.util.List;


/**
 * Sample run:
 * <pre>
 * Given source:
 *  9 5 7
 *  4 8 1
 * and pattern:
 *  9 5
 * matching coordinates=[(0, 0)]
 * ===
 * Given source:
 *  9 5 7
 *  4 8 1
 * and pattern:
 *  7
 *  1
 * matching coordinates=[(2, 0)]
 * ===
 * Given source:
 *  7 2 8 3 4 5 5 8 6 4
 *  6 7 3 1 1 5 8 6 1 9
 *  8 9 8 8 2 4 2 6 4 3
 *  3 8 3 9 5 0 5 3 2 4
 *  9 5 0 9 5 0 5 8 1 3
 *  3 8 4 3 8 4 5 3 8 4
 *  6 4 7 3 5 3 0 2 9 3
 *  7 0 5 3 1 0 6 6 0 1
 *  0 8 3 4 2 8 2 9 5 6
 *  4 6 0 7 9 2 4 1 3 7
 * and pattern:
 *  9 5 0
 *  3 8 4
 *  3 5 3
 * matching coordinates=[(3, 4)]
 * ===
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class Matrix2DPatternExample extends Matrix2DSupport {

  public static void main(String[] args) {
    demo(
        new Matrix2DImpl(2, 3)
            .setRow(0/*row*/, 9, 5, 7)
            .setRow(1/*row*/, 4, 8, 1),
        new Matrix2DImpl(1, 2)
            .setRow(0/*row*/, 9, 5)
    );

    demo(
        new Matrix2DImpl(2, 3)
            .setRow(0/*row*/, 9, 5, 7)
            .setRow(1/*row*/, 4, 8, 1),
        new Matrix2DImpl(2, 1)
            .set(0, 0, 7)
            .set(1, 0, 1)
    );



    demo(
        new Matrix2DImpl(10, 10)
            .setRow(0/*row*/, 7, 2, 8, 3, 4, 5, 5, 8, 6, 4)
            .setRow(1/*row*/, 6, 7, 3, 1, 1, 5, 8, 6, 1, 9)
            .setRow(2/*row*/, 8, 9, 8, 8, 2, 4, 2, 6, 4, 3)
            .setRow(3/*row*/, 3, 8, 3, 9, 5, 0, 5, 3, 2, 4)
            .setRow(4/*row*/, 9, 5, 0, 9, 5, 0, 5, 8, 1, 3)
            .setRow(5/*row*/, 3, 8, 4, 3, 8, 4, 5, 3, 8, 4)
            .setRow(6/*row*/, 6, 4, 7, 3, 5, 3, 0, 2, 9, 3)
            .setRow(7/*row*/, 7, 0, 5, 3, 1, 0, 6, 6, 0, 1)
            .setRow(8/*row*/, 0, 8, 3, 4, 2, 8, 2, 9, 5, 6)
            .setRow(9/*row*/, 4, 6, 0, 7, 9, 2, 4, 1, 3, 7),
        new Matrix2DImpl(3, 3)
            .setRow(0/*row*/, 9, 5, 0)
            .setRow(1/*row*/, 3, 8, 4)
            .setRow(2/*row*/, 3, 5, 3)
    );
  }

  public static void demo(Matrix2D source, Matrix2D pattern) {
    System.out.println("Given source:\n" + source + "and pattern:\n" + pattern +
        "matching coordinates=" + getPatternCoordinates(source, pattern) + "\n===");
  }

  public static List<Coords2D> getPatternCoordinates(Matrix2D source, Matrix2D pattern) {
    final List<Coords2D> coords = new ArrayList<>();

    final int width = source.getColumns() - pattern.getColumns();
    final int height = source.getRows() - pattern.getRows();
    for (int y = 0; y <= height; ++y) {
      for (int x = 0; x <= width; ++x) {
        if (matches(source, x, y, pattern)) {
          coords.add(new Coords2D(x, y));
        }
      }
    }

    return coords;
  }

  public static boolean matches(Matrix2D source, int x, int y, Matrix2D pattern) {
    for (int h = 0; h < pattern.getRows(); ++h) {
      for (int w = 0; w < pattern.getColumns(); ++w) {
        if (source.get(y + h, x + w) != pattern.get(h, w)) {
          return false;
        }
      }
    }

    return true;
  }
}

