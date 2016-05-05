import java.util.*;

/**
 * TODO: complete implementation
 * 
 * @author Alexander Shabanov
 */
public final class TowerOfHanoiExample {

  public static void main(String[] args) {
    demo(4, 3, 2, 1);
  }

  public static void demo(Integer... disks) {
    final Hanoi hanoi = new Hanoi(disks);

    System.out.println("Solving tower of hanoi for disks=" + Arrays.toString(disks));
    hanoi.solve();
  }

  private static final class Hanoi {
    final List<Deque<Integer>> state = new ArrayList<>();

    public Hanoi(Integer[] disks) {
      state.add(new ArrayDeque<>(Arrays.asList(disks)));
      state.add(new ArrayDeque<>());
      state.add(new ArrayDeque<>());
    }

    public boolean solve() {
      System.out.println(" I " + this);

      // check if end state reached
      int empty = 0;
      int ascending = 0;
      for (final Deque<Integer> deque : state) {
        if (deque.isEmpty()) {
          ++empty;
          continue;
        }

        if (isAscending(deque)) {
          ++ascending;
        }
      }

      if ((empty + ascending) == state.size() && ascending == 1) {
        System.out.println("END state");
        return true;
      }

      // try moving disks
      for (int i = 0; i < state.size(); ++i) {
        final Deque<Integer> deque = state.get(i);
        if (deque.isEmpty()) {
          continue;
        }

        final Integer last = deque.pollLast();
        for (int j = 0; j < state.size(); ++j) {
          if (i == j) {
            continue;
          }

          final Deque<Integer> other = state.get(j);
          if (!other.isEmpty() && last >= other.peekLast()) {
            continue;
          }

          other.push(last);
          if (solve()) {
            return true;
          }
          other.pop();
        }

        deque.push(last);
      }

      return false;
    }

    public boolean isReachedFinalState() {
      // check if end state reached
      int empty = 0;
      int ascending = 0;
      for (final Deque<Integer> deque : state) {
        if (deque.isEmpty()) {
          ++empty;
          continue;
        }

        if (isAscending(deque)) {
          ++ascending;
        }
      }

      if ((empty + ascending) == state.size() && ascending == 1) {
        System.out.println("END state");
        return true;
      }

      return false;
    }

    public boolean swap(int from, int to) {
      final Deque<Integer> fromDeque = state.get(from);
      if (fromDeque.isEmpty()) {
        return false;
      }

      final Integer last = fromDeque.pollLast();

      final Deque<Integer> toDeque = state.get(to);
      if (!toDeque.isEmpty() && last > toDeque.peekLast()) {
        return false;
      }

      throw new UnsupportedOperationException();
//      // try moving disks
//      for (int i = 0; i < state.size(); ++i) {
//        final Deque<Integer> deque = state.get(i);
//        if (deque.isEmpty()) {
//          continue;
//        }
//
//        final Integer last = deque.pollLast();
//        for (int j = 0; j < state.size(); ++j) {
//          if (i == j) {
//            continue;
//          }
//
//          final Deque<Integer> other = state.get(j);
//          if (!other.isEmpty() && last >= other.peekLast()) {
//            continue;
//          }
//
//          other.push(last);
//          if (solve()) {
//            return true;
//          }
//          other.pop();
//        }
//
//        deque.push(last);
//      }
    }

    @Override
    public String toString() {
      return "Hanoi{" +
          "state=" + state +
          '}';
    }
  }

  private static boolean isAscending(Iterable<Integer> iterable) {
    final Iterator<Integer> it = iterable.iterator();
    for (Integer prev = it.next(); it.hasNext();) {
      final Integer cur = it.next();
      if (prev > cur) {
        return false;
      }
    }
    return true;
  }
}
