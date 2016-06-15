import java.util.*;

/**
 * @author Alexander Shabanov
 */
public final class StackSortExample {

  public static void main(String[] args) {
    demo(2, 1);
    demo(1, 2);

    demo(getShuffledIntegers(4123342895671398746L));
    demo(getShuffledIntegers(-4123342895671398746L));
    demo(getShuffledIntegers(1L));
    demo(getShuffledIntegers(-1L));
  }

  private static Integer[] getShuffledIntegers(long seed) {
    final List<Integer> buf = new ArrayList<>(10);
    for (int i = 1; i < 10; ++i) {
      buf.add(i);
    }
    Collections.shuffle(buf, new Random(seed));
    return buf.toArray(new Integer[buf.size()]);
  }

  private static void demo(Integer... values) {
    final Deque<Integer> deque = new ArrayDeque<>(Arrays.asList(values));
    System.out.println("Input=" + deque + " sorted stack=" + sortStack(deque));
  }

  //
  // Private
  //

  private static Deque<Integer> sortStack(Deque<Integer> values) {
    final Deque<Integer> buffer = new ArrayDeque<>(values); // use only push and pop
    final Deque<Integer> result = new ArrayDeque<>();
    final Deque<Integer> temp = new ArrayDeque<>();

    while (!buffer.isEmpty()) {
      final Integer candidate = buffer.pop();

      boolean added = false;

      do {
        if (result.isEmpty()) {
          result.push(candidate);
          added = true;
        } else {
          final Integer head = result.peek();
          if (head >= candidate) {
            result.push(candidate);
            added = true;
          } else {
            temp.push(result.pop());
          }
        }
      } while (!added);

      while (!temp.isEmpty()) {
        result.push(temp.pop());
      }
    }

    return result;
  }
}
