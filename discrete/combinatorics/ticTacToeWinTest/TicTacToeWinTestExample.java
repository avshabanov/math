import java.util.Arrays;

/**
 * Sample run:
 *
 * <pre>
 * Demo1 WinCondition=X
 * Demo2 WinCondition=EMPTY
 * Demo3 WinCondition=O
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class TicTacToeWinTestExample {

  public static void main(String[] args) {
    demo1();
    demo2();
    demo3();
  }

  private static void demo1() {
    final Field field = new Field();
    field
        .x(0, 1).x(1, 1).x(2, 1)
        .o(0, 0).o(2, 2);

    final Cell winCondition = field.getWinCondition();

    if (winCondition != Cell.X) {
      throw new AssertionError("demo1");
    }

    System.out.println("Demo1 WinCondition=" + winCondition);
  }

  private static void demo2() {
    final Field field = new Field();
    field
        .x(0, 1).x(2, 1)
        .o(0, 0).o(2, 2);

    final Cell winCondition = field.getWinCondition();

    if (winCondition != Cell.EMPTY) {
      throw new AssertionError("demo2");
    }

    System.out.println("Demo2 WinCondition=" + winCondition);
  }

  private static void demo3() {
    final Field field = new Field();
    field
        .x(0, 1).x(2, 1)
        .o(0, 2).o(1, 1).o(2, 0);

    final Cell winCondition = field.getWinCondition();

    if (winCondition != Cell.O) {
      throw new AssertionError("demo3");
    }

    System.out.println("Demo3 WinCondition=" + winCondition);
  }

  private enum Cell {
    X,
    O,
    EMPTY
  }

  private static final class Field {
    final Cell[] cells;
    final int dim;

    public Field(int dim) {
      this.dim = dim;
      this.cells = new Cell[dim * dim];
      Arrays.fill(this.cells, Cell.EMPTY);
    }

    public Field() {
      this(3);
    }

    public Field cell(int w, int h, Cell cell) {
      cells[w + h * dim] = cell;
      return this;
    }

    public Cell cellAt(int w, int h) {
      return cells[w + h * dim];
    }

    public Field x(int w, int h) {
      return cell(w, h, Cell.X);
    }

    public Field o(int w, int h) {
      return cell(w, h, Cell.O);
    }

    public Cell getWinCondition() {
      horizontal: for (int h = 0; h < dim; ++h) {
        final Cell res = cellAt(0, h);
        if (res == Cell.EMPTY) {
          continue;
        } for (int w = 1; w < dim; ++w) {
          if (res != cellAt(w, h)) {
            continue horizontal;
          }
        }
        return res;
      }

      vertical: for (int w = 0; w < dim; ++w) {
        final Cell res = cellAt(w, 0);
        if (res == Cell.EMPTY) {
          continue;
        } for (int h = 1; h < dim; ++h) {
          if (res != cellAt(w, h)) {
            continue vertical;
          }
        }
        return res;
      }

      leftRight: {
        final Cell res = cellAt(0, 0);
        if (res == Cell.EMPTY) {
          break leftRight;
        } for (int k = 1; k < dim; ++k) {
          if (res != cellAt(k, k)) {
            break leftRight;
          }
        }
        return res;
      }

      rightLeft: {
        final Cell res = cellAt(0, dim - 1);
        if (res == Cell.EMPTY) {
          break rightLeft;
        } else for (int k = 1; k < dim; ++k) {
          if (res != cellAt(dim - k - 1, k)) {
            break rightLeft;
          }
        }
        return res;
      }

      return Cell.EMPTY;
    }
  }
}
