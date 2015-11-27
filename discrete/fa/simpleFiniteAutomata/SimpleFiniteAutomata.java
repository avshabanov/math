import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

/**
 * @author Alexander Shabanov
 */
public final class SimpleFiniteAutomata {

  public static void main(String[] args) {
    final FooStateImpl s4 = new FooStateImpl("s4");

    final FooStateImpl s3_2 = new FooStateImpl("s3_2");
    s3_2.addMoveStateData(FooInput.D, s4, () -> System.out.println("[Moving to state 4]"));

    final FooStateImpl s3_1 = new FooStateImpl("s3_1");
    s3_1.addMoveStateData(FooInput.D, s4, () -> System.out.println("[Moving to state 4]"));

    final FooStateImpl s2 = new FooStateImpl("s2");
    s2.addMoveStateData(FooInput.B, s3_1, () -> System.out.println("[Moving to state 3-1]"));
    s2.addMoveStateData(FooInput.C, s3_2, () -> System.out.println("[Moving to state 3-2]"));

    final FooStateImpl s1 = new FooStateImpl("s1");
    s1.addMoveStateData(FooInput.A, s2, () -> System.out.println("[Moving to state 2]"));
    final FooFiniteAutomataImpl fooFiniteAutomata = new FooFiniteAutomataImpl(s1);

    runAutomata(fooFiniteAutomata, FooInput.A, FooInput.B, FooInput.D);
    runAutomata(fooFiniteAutomata, FooInput.A, FooInput.C, FooInput.D);
  }

  //
  // Abstract, idealized model of finite state machine (FA)
  //

  private interface Input {
  }

  private interface State<TInput extends Input, TState extends State> {
    boolean isFinite();
    TState next(TInput input);
  }

  private interface FiniteAutomata<TState extends State> {
    TState getInitialState();
  }

  //
  // Generic FA runner
  //

  @SafeVarargs
  private static <TInput extends Input, TState extends State> void runAutomata(
      FiniteAutomata<? extends State<TInput, TState>> finiteAutomata, TInput... inputSequence) {
    State<TInput, TState> next = finiteAutomata.getInitialState();
    System.out.println("First state=" + next);

    for (final TInput input : inputSequence) {
      //noinspection unchecked
      next = next.next(input);
      System.out.println("Next state=" + next + ", isFinite=" + next.isFinite() + " for input=" + input);
    }

    System.out.println("===");
  }

  //
  // Foo Finite Automation Interface and Implementation
  //

  // Foo / Interface

  private enum FooInput implements Input {
    A, B, C, D
  }

  private interface FooState extends State<FooInput, FooState> {}

  private interface FooFiniteAutomata extends FiniteAutomata<FooState> {}

  // Foo / Implementation

  private static final class FooStateImpl implements FooState {
    private static final class MoveStateData {
      final Runnable runnable;
      final FooState next;

      public MoveStateData(Runnable runnable, FooState next) {
        this.runnable = Objects.requireNonNull(runnable);
        this.next = Objects.requireNonNull(next);
      }
    }

    private final Map<FooInput, MoveStateData> stateMap = new HashMap<>();
    private final String stateName;

    public FooStateImpl(String stateName) {
      this.stateName = stateName;
    }

    public void addMoveStateData(FooInput input, FooState nextState, Runnable runnable) {
      stateMap.put(input, new MoveStateData(runnable, nextState));
    }

    @Override
    public boolean isFinite() {
      return stateMap.isEmpty();
    }

    @Override
    public FooState next(FooInput input) {
      final MoveStateData moveStateData = stateMap.get(input);
      if (moveStateData == null) {
        throw new IllegalStateException("Invalid input");
      }
      moveStateData.runnable.run();
      return moveStateData.next;
    }

    @Override
    public String toString() {
      return "" + '<' + stateName + '>';
    }
  }

  private static final class FooFiniteAutomataImpl implements FooFiniteAutomata {

    private final FooState initialState;

    public FooFiniteAutomataImpl(FooState initialState) {
      this.initialState = Objects.requireNonNull(initialState);
    }

    @Override
    public FooState getInitialState() {
      return initialState;
    }
  }
}
