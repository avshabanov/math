import ticTacToeSupport.Cell;
import ticTacToeSupport.ArrayBasedField;
import ticTacToeSupport.Field;
import ticTacToeSupport.WinCondition;

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
    expectWinCondition("Demo1", Cell.X, new ArrayBasedField(3)
        .x(0, 1).x(1, 1).x(2, 1)
        .o(0, 0).o(2, 2));
  }

  private static void demo2() {
    expectWinCondition("Demo2", Cell.EMPTY, new ArrayBasedField()
        .x(0, 1).x(2, 1)
        .o(0, 0).o(2, 2));
  }

  private static void demo3() {
    expectWinCondition("Demo3", Cell.O, new ArrayBasedField()
        .x(0, 1).x(2, 1)
        .o(0, 2).o(1, 1).o(2, 0));
  }

  private static void expectWinCondition(String name, Cell expectedWinCondition, Field field) {
    final Cell winCondition = WinCondition.test(field);

    if (winCondition != expectedWinCondition) {
      throw new AssertionError(name + ": win expected=" + expectedWinCondition + ", actual=" + winCondition);
    }

    System.out.println(name + " win condition=" + winCondition);
  }
}
