import support.Matrix2DSupport;

import java.util.Collections;
import java.util.List;

@SuppressWarnings("NullableProblems")
public class TwoDimensionMatrixSort extends Matrix2DSupport {

  private static void displaySortedMatrix(Matrix2D m) {
    System.out.println("Matrix=\n" + m);

    final List<Integer> mList = asList(m);
    System.out.println("MatrixAsList=" + mList);

    Collections.sort(mList);
    System.out.println("SortedMatrixAsList=" + mList);

    System.out.println("SortedMatrix=\n" + m);

    System.out.println("===");
  }

  public static void main(String[] args) {
    Matrix2D m = new Matrix2DImpl(2, 3);
    m.set(0, 0, 9).set(0, 1, 5).set(0, 2, 7);
    m.set(1, 0, 4).set(1, 1, 8).set(1, 2, 1);
    displaySortedMatrix(m);

    m = new Matrix2DImpl(3, 1);
    m.set(0, 0, 9).set(1, 0, 5).set(2, 0, 7);
    displaySortedMatrix(m);

    m = new Matrix2DImpl(3, 2);
    m.set(0, 0, 9).set(0, 1, 5);
    m.set(1, 0, 4).set(1, 1, 8);
    m.set(2, 0, 7).set(2, 1, 1);
    displaySortedMatrix(m);
  }
}
