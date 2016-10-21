package ticTacToeSupport;

/**
 * @author Alexander Shabanov
 */
public final class WinCondition {
  private WinCondition() {}

  public static Cell test(Field field) {
    final int dim = field.getDimension();
    
    horizontal: for (int h = 0; h < dim; ++h) {
      final Cell res = field.cellAt(0, h);
      if (res == Cell.EMPTY) {
        continue;
      } for (int w = 1; w < dim; ++w) {
        if (res != field.cellAt(w, h)) {
          continue horizontal;
        }
      }
      return res;
    }

    vertical: for (int w = 0; w < dim; ++w) {
      final Cell res = field.cellAt(w, 0);
      if (res == Cell.EMPTY) {
        continue;
      } for (int h = 1; h < dim; ++h) {
        if (res != field.cellAt(w, h)) {
          continue vertical;
        }
      }
      return res;
    }

    leftRight: {
      final Cell res = field.cellAt(0, 0);
      if (res == Cell.EMPTY) {
        break leftRight;
      } for (int k = 1; k < dim; ++k) {
        if (res != field.cellAt(k, k)) {
          break leftRight;
        }
      }
      return res;
    }

    rightLeft: {
      final Cell res = field.cellAt(0, dim - 1);
      if (res == Cell.EMPTY) {
        break rightLeft;
      } else for (int k = 1; k < dim; ++k) {
        if (res != field.cellAt(dim - k - 1, k)) {
          break rightLeft;
        }
      }
      return res;
    }

    return Cell.EMPTY;
  }
}
