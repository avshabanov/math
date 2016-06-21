import support.Matrix2DSupport;

/**
 * Sample run:
 * <pre>
 * [Before] Matrix =
 *  0 1
 *  2 3
 *
 * [After Rot90] Matrix =
 *  2 0
 *  3 1
 *
 * [Before] Matrix =
 *  0 1 2
 *  3 4 5
 *  6 7 8
 *
 * [After Rot90] Matrix =
 *  6 3 0
 *  7 4 1
 *  8 5 2
 *
 * [Before] Matrix =
 *  0 1 2 3
 *  4 5 6 7
 *  8 9 10 11
 *  12 13 14 15
 *
 * [After Rot90] Matrix =
 *  12 8 4 0
 *  13 9 5 1
 *  14 10 6 2
 *  15 11 7 3
 * </pre>
 * @author Alexander Shabanov
 */
public final class Matrix2DRotationExample extends Matrix2DSupport {

  public static void main(String[] args) {
    demo2x2();
    demo3x3();
    demo4x4();
  }

  public static void demo2x2() {
    final Matrix2D m = new Matrix2DImpl(2, 2);
    m.set(0, 0, 0).set(0, 1, 1);
    m.set(1, 0, 2).set(1, 1, 3);

    System.out.println("[Before] Matrix =\n" + m);
    rotateInplace90(m);
    System.out.println("[After Rot90] Matrix =\n" + m);
  }

  public static void demo3x3() {
    final Matrix2D m = new Matrix2DImpl(3, 3);
    m.set(0, 0, 0).set(0, 1, 1).set(0, 2, 2);
    m.set(1, 0, 3).set(1, 1, 4).set(1, 2, 5);
    m.set(2, 0, 6).set(2, 1, 7).set(2, 2, 8);

    System.out.println("[Before] Matrix =\n" + m);
    rotateInplace90(m);
    System.out.println("[After Rot90] Matrix =\n" + m);
  }

  public static void demo4x4() {
    final Matrix2D m = new Matrix2DImpl(4, 4);
    m.set(0, 0, 0) .set(0, 1, 1) .set(0, 2, 2) .set(0, 3, 3);
    m.set(1, 0, 4) .set(1, 1, 5) .set(1, 2, 6) .set(1, 3, 7);
    m.set(2, 0, 8) .set(2, 1, 9) .set(2, 2, 10).set(2, 3, 11);
    m.set(3, 0, 12).set(3, 1, 13).set(3, 2, 14).set(3, 3, 15);

    System.out.println("[Before] Matrix =\n" + m);
    rotateInplace90(m);
    System.out.println("[After Rot90] Matrix =\n" + m);
  }

  private static void rotateInplace90(Matrix2D matrix2D) {
    final int n = matrix2D.getColumns();
    if (n != matrix2D.getRows()) {
      throw new IllegalArgumentException("Only square matrices are supported");
    }

    for (int offset = 0; offset < (n / 2); ++offset) {
      final int last = n - 1;
      final int lim = n - offset * 2 - 1;

      for (int i = 0; i < lim; ++i) {
        final int p1 = matrix2D.get(offset, offset + i);
        final int p2 = matrix2D.get(offset + i, last - offset);
        final int p3 = matrix2D.get(last - offset, last - offset - i);
        final int p4 = matrix2D.get(last - offset - i, offset);

        // set
        matrix2D.set(offset + i, last - offset, p1);
        matrix2D.set(last - offset, last - offset - i, p2);
        matrix2D.set(last - offset - i, offset, p3);
        matrix2D.set(offset, offset + i, p4);
      }
    }
  }
}
