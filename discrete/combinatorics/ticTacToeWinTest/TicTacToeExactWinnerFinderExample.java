
import ticTacToeSupport.ArrayBasedField;
import ticTacToeSupport.Cell;
import ticTacToeSupport.Field;
import ticTacToeSupport.WinCondition;

/**
 * Brute force tic tac toe solution finder demo.
 * <p>
 * Given a position and best possible play for both players, finds out who would win.
 * </p>
 *
 * @author Alexander Shabanov
 */
public final class TicTacToeExactWinnerFinderExample {

  public static void main(String[] args) {
    demo1();
    demo2();
    demo3();
  }

  private static void demo1() {
    final Cell cell = getWinner(new ArrayBasedField()
            .x(0, 0).x(0, 2).x(2, 2).o(1, 0).o(1, 2),
        true);

    System.out.println("Winner = " + cell);
  }

  private static void demo2() {
    final Cell cell = getWinner(new ArrayBasedField()
            .o(1, 1).x(1, 2),
        true);

    System.out.println("Winner = " + cell);
  }

  private static void demo3() {
    final Cell cell = getWinner(new ArrayBasedField()
            .x(1, 1),
        false);

    System.out.println("Winner = " + cell);
  }

  private static Cell getWinner(Field field, boolean nextMoveX) {
    // TODO: optimize, call win condition test only for leaf recursion calls - e.g. account for recursion depth
    Cell win = WinCondition.test(field);
    if (win != Cell.EMPTY) {
      return win;
    }

    for (int w = 0; w < field.getDimension(); ++w) {
      for (int h = 0; h < field.getDimension(); ++h) {
        Cell cell = field.cellAt(w, h);
        if (cell != Cell.EMPTY) {
          continue;
        }

        field.setCell(w, h, nextMoveX ? Cell.X : Cell.O);
        final Cell other = getWinner(field, !nextMoveX);
        if (other == Cell.EMPTY) {
          return other; // draw
        }

        if (win == Cell.EMPTY) {
          // initialization
          win = other;
          continue;
        }

        if (win != other) {
          return Cell.EMPTY; // draw detection - different win scenarios
        }
      }
    }

    return win;
  }
}