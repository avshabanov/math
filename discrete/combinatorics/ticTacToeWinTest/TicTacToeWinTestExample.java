import java.util.Arrays;

/**
 * @author Alexander Shabanov
 */
public final class TicTacToeWinTestExample {

  public static void main(String[] args) {

  }

  private enum Cell {
    X,
    O,
    EMPTY
  }

  public static final class Field {
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

    public Field x(int w, int h) {
      return cell(w, h, Cell.X);
    }

    public Field o(int w, int h) {
      return cell(w, h, Cell.O);
    }

    public Cell checkWinCondition() {
      // check horizontal
      for (int h = 0; h < dim; ++h) {
        int index = h * dim;
        Cell res = cells[index];
        for (int w = 1; w < dim; ++w) {
          if (res != cells[++index]) {
            res = Cell.EMPTY;
            break;
          }
        }
        if (res != Cell.EMPTY) {
          return res;
        }
      }

      // check vertical
      // TODO: reduce repeated code
      for (int w = 0; w < dim; ++w) {
        int index = w;
        Cell res = cells[index];
        for (int h = 1; h < dim; ++h) {
          index += dim;
          if (res != cells[index]) {
            res = Cell.EMPTY;
            break;
          }
        }
        if (res != Cell.EMPTY) {
          return res;
        }
      }

      // check left-right diagonal
      {
        Cell res = cells[0];
        for (int k = 1; k < dim; ++k) {
          ;
        }
      }


      return Cell.EMPTY;
    }
  }
}
