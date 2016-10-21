import ticTacToeSupport.ArrayBasedField;
import ticTacToeSupport.Cell;
import ticTacToeSupport.Field;
import ticTacToeSupport.WinCondition;

/**
 * Returns most probable winner in tic-tac-toe game.
 *
 * @author Alexander Shabanov
 */
public final class TicTacToeWinnerFinderExample {

  public static void main(String[] args) {
    demo1();
    demo2();
    demo3();
  }

  private static void demo1() {
    final WinCell cell = getPotentialWinner(new ArrayBasedField()
          .x(0, 0).x(0, 2).x(2, 2).o(1, 0).o(1, 2),
        0, true);

    System.out.println("Potential winner = " + cell.cell);
  }

  private static void demo2() {
    final WinCell cell = getPotentialWinner(new ArrayBasedField()
            .o(1, 1).x(1, 2),
        0, true);

    System.out.println("Potential winner = " + cell.cell);
  }

  private static void demo3() {
    final WinCell cell = getPotentialWinner(new ArrayBasedField()
            .o(0, 0).x(2, 2),
        0, true);

    System.out.println("Potential winner = " + cell.cell);
  }

  private static WinCell getPotentialWinner(Field field, int depth, boolean nextCellO) {
    Cell cell = WinCondition.test(field);
    if (cell != Cell.EMPTY) {
      return new WinCell(cell, depth);
    }

    WinCell minCandidate = null;
    for (int w = 0; w < field.getDimension(); ++w) {
      for (int h = 0; h < field.getDimension(); ++h) {
        cell = field.cellAt(w, h);
        if (cell != Cell.EMPTY) {
          continue;
        }

        field.setCell(w, h, nextCellO ? Cell.O : Cell.X);
        final WinCell candidate = getPotentialWinner(field, depth + 1, !nextCellO);
        if (minCandidate == null || candidate.depth < minCandidate.depth ||
            (minCandidate.depth == candidate.depth && candidate.cell == Cell.EMPTY)) {
          minCandidate = candidate;
        }
      }
    }

    return minCandidate;
  }

  private static class WinCell {
    final Cell cell;
    final int depth;

    WinCell(Cell cell, int depth) {
      this.cell = cell;
      this.depth = depth;
    }
  }
}
