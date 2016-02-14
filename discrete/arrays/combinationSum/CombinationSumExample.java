import java.lang.UnsupportedOperationException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

/**
 * Sample output:
 * <pre>
 * Given array=[] and value=1 sum combinations=[]
 * Given array=[1] and value=1 sum combinations=[[1]]
 * Given array=[1, 2] and value=7 sum combinations=[]
 * Given array=[3, 3, 2, 1, 2] and value=3 sum combinations=[[1, 2], [3]]
 * Given array=[5, 4, 3, 2, 1, 6, 5, 4, 8, 1, 7, 2] and value=7 sum combinations=[[1, 2, 4], [3, 4], [2, 5], [1, 6], [7]]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class CombinationSumExample {

  public static void main(String[] args) {
    demo(Collections.emptyList(), 1);
    demo(Collections.singletonList(1), 1);
    demo(Arrays.asList(1, 2), 7);
    demo(Arrays.asList(3, 3, 2, 1, 2), 3);
    demo(Arrays.asList(5, 4, 3, 2, 1, 6, 5, 4, 8, 1, 7, 2), 7);
  }

  public static void demo(List<Integer> ints, int value) {
    final List<List<Integer>> result = getCombinationSumRecursive(ints, value);
    System.out.println("Given array=" + ints + " and value=" + value + " sum combinations=" + result);
  }

  public static List<List<Integer>> getCombinationSumRecursive(List<Integer> ints, int value) {
    final Set<Integer> s = new TreeSet<>(ints);
    final List<Integer> sortedListWithoutDuplicates = new ArrayList<>(s);

    final Set<List<Integer>> result = new HashSet<>();
    findRecursive(0, new ArrayList<>(), 0, Collections.unmodifiableList(sortedListWithoutDuplicates), value, result);
    return new ArrayList<>(result);
  }

  private static void findRecursive(final int sum,
                                    final List<Integer> current,
                                    final int pos,
                                    final List<Integer> ints,
                                    final int value,
                                    final Set<List<Integer>> result) {
    if (sum == value) {
      result.add(new ArrayList<>(current));
      return;
    }

    for (int i = pos; i < ints.size(); ++i) {
      final Integer val = ints.get(i);
      final int newSum = sum + val;

      if (newSum > value) {
        break;
      }

      current.add(val);
      findRecursive(newSum, current, i + 1, ints, value, result);
      current.remove(current.size() - 1);
    }
  }

  public static List<List<Integer>> getCombinationSumNonRecursive(List<Integer> ints, int value) {
    // TODO: impl
    throw new UnsupportedOperationException();
  }
}
