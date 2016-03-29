package support;

import java.util.AbstractList;
import java.util.List;

/**
 * Encapsulates support stuff for 2D matrix examples.
 *
 * @author Alexander Shabanov
 */
public abstract class Matrix2DSupport {

  public interface Matrix2D {
    int getRows();
    int getColumns();
    int get(int row, int column);
    Matrix2D set(int row, int column, int value);
    Matrix2D setRow(int row, int... values);
  }

  public static final class Matrix2DImpl implements Matrix2D {
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
    public Matrix2D setRow(int row, int... values) {
      for (int i = 0; i < values.length; ++i) {
        set(row, i, values[i]);
      }
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

  public static List<Integer> asList(final Matrix2D m) {
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

  public static final class Coords2D {
    private final int x;
    private final int y;

    public Coords2D(int x, int y) {
      this.x = x;
      this.y = y;
    }

    public int getX() {
      return x;
    }

    public int getY() {
      return y;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;

      final Coords2D coords2D = (Coords2D) o;

      return getX() == coords2D.getY() && getY() == coords2D.getY();

    }

    @Override
    public int hashCode() {
      int result = getX();
      result = 31 * result + getY();
      return result;
    }

    @Override
    public String toString() {
      return "("  + getX() + ", " + getY() + ')';
    }
  }
}
