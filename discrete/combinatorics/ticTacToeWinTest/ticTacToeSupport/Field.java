package ticTacToeSupport;

/**
 * @author Alexander Shabanov
 */
public interface Field {

  int getDimension();

  Cell cellAt(int w, int h);

  Field setCell(int w, int h, Cell cell);

  default Field x(int w, int h) {
    return setCell(w, h, Cell.X);
  }

  default Field o(int w, int h) {
    return setCell(w, h, Cell.O);
  }
}
