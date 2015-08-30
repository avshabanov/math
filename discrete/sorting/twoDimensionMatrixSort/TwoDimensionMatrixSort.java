import java.util.AbstractList;
import java.util.Collections;
import java.util.List;

@SuppressWarnings("NullableProblems")
public class TwoDimensionMatrixSort {
  private interface Matrix2D {
    int getRows();
    int getColumns();
    int get(int row, int column);
    Matrix2D set(int row, int column, int value);
  }

  private static final class Matrix2DImpl implements Matrix2D {
    private final int[] arr;
    private final int rows;
    private final int columns;

    public Matrix2DImpl(int rows, int columns) {
      this.rows = rows;
      this.columns = columns;
      this.arr = new int[rows * columns];
    }

    @Override
    public int getRows() {
      return this.rows;
    }

    @Override
    public int getColumns() {
      return this.columns;
    }

    @Override
    public int get(int row, int column) {
      if (row >= this.rows || column >= this.columns) {
        throw new IllegalArgumentException();
      }
      return this.arr[this.rows * column + row];
    }

    @Override
    public Matrix2D set(int row, int column, int value) {
      if (row >= this.rows || column >= this.columns) {
        throw new IllegalArgumentException();
      }
      this.arr[this.rows * column + row] = value;
      return this;
    }

    @Override
    public String toString() {
      final StringBuilder builder = new StringBuilder(rows * columns * 5 + 10);

      for (int r = 0; r < getRows(); ++r) {
        for (int c = 0; c < getColumns(); ++c) {
          final int val = get(r, c);
          builder.append(' ').append(val);
        }
        builder.append('\n');
      }

      return builder.toString();
    }
  }

  private static List<Integer> asList(final Matrix2D m) {
    return new AbstractList<Integer>() {
      @Override
      public Integer get(int index) {
        final int row = index / m.getColumns();
        final int column = index - (row * m.getColumns());
        return m.get(row, column);
      }

      @Override
      public Integer set(int index, Integer element) {
        final int row = index / m.getColumns();
        final int column = index - (row * m.getColumns());

        final int prevVal = get(index);
        m.set(row, column, element);
        return prevVal;
      }

      @Override
      public int size() {
        return m.getColumns() * m.getRows();
      }
    };
  }

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
