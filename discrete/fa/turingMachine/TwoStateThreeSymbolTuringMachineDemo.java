import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Example: https://en.wikipedia.org/wiki/Wolfram%27s_2-state_3-symbol_Turing_machine
 *
 * Definition:
 * <pre>
 *      A	      B
 * 0	P1,R,B	P2,L,A
 * 1	P2,L,A	P2,R,B
 * 2	P1,L,A	P0,R,A
 * The (2,3) Turing machine:
 * Has no halt state;
 * Is trivially related to 23 other machines by interchange of states, colors and directions.
 * </pre>
 *
 * Sample run:
 *
 * <pre>
 * == Turing Machine Demo ==
 * State=A, pos=0, tape=[All Zeroes]
 * state: B, tape: pos=  1, contents=1
 * state: A, tape: pos=  0, contents=1
 * state: A, tape: pos= -1, contents=02
 * state: B, tape: pos=  0, contents=12
 * state: A, tape: pos=  1, contents=10
 * state: A, tape: pos=  0, contents=10
 * state: B, tape: pos=  1, contents=11
 * state: B, tape: pos=  2, contents=112
 * state: A, tape: pos=  1, contents=112
 * state: A, tape: pos=  0, contents=111
 * state: A, tape: pos= -1, contents=121
 * state: A, tape: pos= -2, contents=0221
 * state: B, tape: pos= -1, contents=1221
 * state: A, tape: pos=  0, contents=1021
 * state: A, tape: pos= -1, contents=1011
 * state: B, tape: pos=  0, contents=1111
 * ===
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class TwoStateThreeSymbolTuringMachineDemo {

  public static void main(String[] args) {
    System.out.println("== Turing Machine Demo ==");

    demo1();
  }

  private static void demo1() {
    System.out.println("State=A, pos=0, tape=[All Zeroes]");

    final Tape tape = new SparseTape(0, Collections.emptyList());
    final Interpreter interpreter = new Interpreter(State.A, tape);

    // run 10 steps of machine
    interpreter.steps(16);

    System.out.println("===");
  }

  //
  // Private
  //

  // interface

  private enum Symbol {
    ZERO,
    ONE,
    TWO
  }

  private enum State {
    A,
    B
  }

  private interface Tape {

    void moveLeft();

    void moveRight();

    Symbol read();

    void print(Symbol symbol);
  }

  // implementation

  private static final class SparseTape implements Tape {
    private int pos;
    private Map<Integer, Symbol> symbols = new HashMap<>(100);
    private int leftmostKnownPos = 0;
    private int rightmostKnownPos = 0;

    public SparseTape(int pos, List<Symbol> initialSymbols) {
      this.pos = pos;
      for (int i = 0; i < initialSymbols.size(); ++i) {
        symbols.put(i, initialSymbols.get(i));
      }

      leftmostKnownPos = Math.min(pos, 0);
      rightmostKnownPos = Math.max(pos, initialSymbols.size());
    }

    @Override
    public void moveLeft() {
      this.pos = this.pos - 1;
      this.leftmostKnownPos = Math.min(this.leftmostKnownPos, this.pos);
    }

    @Override
    public void moveRight() {
      this.pos = this.pos + 1;
      this.rightmostKnownPos = Math.max(this.rightmostKnownPos, this.pos);
    }

    @Override
    public Symbol read() {
      final Symbol s = symbols.get(this.pos);
      return s == null ? Symbol.ZERO : s;
    }

    @Override
    public void print(Symbol symbol) {
      symbols.put(this.pos, symbol);
    }

    @Override
    public String toString() {
      final StringBuilder builder = new StringBuilder(rightmostKnownPos - leftmostKnownPos + 10);

      builder.append("pos=").append(String.format("%3d", pos)).append(", contents=");
      for (int i = leftmostKnownPos; i < rightmostKnownPos; ++i) {
        final Symbol symbol = symbols.get(i);

        if (symbol == null || symbol == Symbol.ZERO) {
          builder.append('0');
          continue;
        }

        switch (symbol) {
          case ONE:
            builder.append('1');
            break;
          case TWO:
            builder.append('2');
            break;
        }
      }

      return builder.toString();
    }
  }

  private static final class Interpreter {
    private final Tape tape;
    private State state;

    public Interpreter(State initialState, Tape tape) {
      this.state = initialState;
      this.tape = tape;
    }

    public void steps(int maxSteps) {
      for (int i = 0; i < maxSteps; ++i) {
        step();
      }
    }

    public void step() {
      final Symbol symbol = this.tape.read();
      switch (state) {
        case A:
          switch (symbol) {
            case ZERO:
              // P1,R,B
              this.tape.print(Symbol.ONE);
              this.tape.moveRight();
              this.state = State.B;
              break;
            case ONE:
              // P2,L,A
              this.tape.print(Symbol.TWO);
              this.tape.moveLeft();
              this.state = State.A;
              break;
            case TWO:
              // P1,L,A
              this.tape.print(Symbol.ONE);
              this.tape.moveLeft();
              this.state = State.A;
              break;
          }
          break;

        case B:
          switch (symbol) {
            case ZERO:
              // P2,L,A
              this.tape.print(Symbol.TWO);
              this.tape.moveLeft();
              this.state = State.A;
              break;
            case ONE:
              // P2,R,B
              this.tape.print(Symbol.TWO);
              this.tape.moveRight();
              this.state = State.B;
              break;
            case TWO:
              // P0,R,A
              this.tape.print(Symbol.ZERO);
              this.tape.moveRight();
              this.state = State.A;
              break;
          }
          break;
      }

      System.out.println("state: " + state + ", tape: " + tape);
    }
  }
}
