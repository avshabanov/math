import java.util.*;

/**
 * Brute-force tower of hanoi example.
 * TODO: optimize
 * 
 * @author Alexander Shabanov
 */
public final class TowerOfHanoiExample {

  public static void main(String[] args) {
    demo(3, 2, 1);
  }

  public static void demo(Integer... disks) {
    final Hanoi hanoi = new Hanoi(disks);

    System.out.println("Solving tower of hanoi for disks=" + Arrays.toString(disks));
    hanoi.solve();
  }

  private static final class Hanoi {
    List<List<Integer>> state = new ArrayList<>();
    // TODO: can be folded into long
    final Set<List<List<Integer>>> prevStates = new LinkedHashSet<>();

    public Hanoi(Integer[] disks) {
      state.add(Collections.unmodifiableList(Arrays.asList(disks)));
      state.add(Collections.emptyList());
      state.add(Collections.emptyList());
    }

    public boolean solve() {
      //System.out.println(" I " + this);

      // check if end state reached
      if (isFinalStateReached()) {
        for (final List<List<Integer>> deque : prevStates) {
          System.out.println(" I " + deque);
        }
        System.out.println("Reached END state: " + state);
        return true;
      }

      // try moving disks
      for (int sourceIndex = 0; sourceIndex < state.size(); ++sourceIndex) {
        final List<Integer> source = state.get(sourceIndex);
        if (source.isEmpty()) {
          continue;
        }

        final WithoutLastResult withoutLast = withoutLast(source);
        final Integer last = withoutLast.last;
        for (int targetIndex = 0; targetIndex < state.size(); ++targetIndex) {
          if (sourceIndex == targetIndex) {
            continue;
          }

          final List<Integer> target = state.get(targetIndex);
          if (!target.isEmpty() && last > target.get(target.size() - 1)) {
            continue;
          }

          final List<Integer> newTarget = withLast(target, last);

          final List<List<Integer>> newState = new ArrayList<>(state);
          newState.set(sourceIndex, withoutLast.newList);
          newState.set(targetIndex, newTarget);

          if (prevStates.contains(newState)) {
            continue;
          }

          prevStates.add(newState);

          final List<List<Integer>> oldState = state;
          state = newState;
          if (solve()) {
            return true;
          }

          prevStates.remove(newState);
          state = oldState;
        }
      }

      return false;
    }

    public boolean isFinalStateReached() {
      int ascendingIndex = -1;
      for (int i = 0; i < state.size(); ++i) { // state.stream().filter(List::isEmpty).count();
        final List<Integer> deque = state.get(i);
        if (deque.isEmpty()) {
          continue;
        }

        if (ascendingIndex < 0) {
          ascendingIndex = i;
          continue;
        }

        return false;
      }

      return ascendingIndex > 0;
    }

    @Override
    public String toString() {
      return "Hanoi{" +
          "state=" + state +
          '}';
    }
  }

  private static final class WithoutLastResult {
    final List<Integer> newList;
    final Integer last;

    public WithoutLastResult(List<Integer> newList, Integer last) {
      this.newList = newList;
      this.last = last;
    }
  }

  private static WithoutLastResult withoutLast(List<Integer> list) {
    if (list.isEmpty()) {
      throw new IllegalStateException();
    }

    final int newSize = list.size() - 1;
    final Integer last = list.get(newSize);
    final List<Integer> newList;
    if (newSize == 0) {
      newList = Collections.emptyList();
    } else if (newSize == 1) {
      newList = Collections.singletonList(list.get(0));
    } else {
      newList = Collections.unmodifiableList(new ArrayList<>(list.subList(0, newSize)));
    }
    return new WithoutLastResult(newList, last);
  }

  private static List<Integer> withLast(List<Integer> list, Integer element) {
    if (list.size() == 0) {
      return Collections.singletonList(element);
    }

    final List<Integer> result = new ArrayList<>(list.size() + 1);
    result.addAll(list);
    result.add(element);
    return Collections.unmodifiableList(result);
  }
}
