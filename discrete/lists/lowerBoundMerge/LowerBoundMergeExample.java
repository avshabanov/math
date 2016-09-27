import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Illustration of limited merge:
 * <pre>
 * Given two sorted lists (or arrays) and a number k, create an algorithm to fetch the least k numbers of the two lists.
 * - from https://careercup.com/question?id=5159328785891328
 * </pre>
 */
public final class LowerBoundMergeExample {

  public static void main(String[] args) {
    demo(new int[] { 1, 3, 5, 7 }, new int[] { 2, 4, 6, 8 }, 4);
    demo(new int[] { 1, 10 }, new int[] { 2, 3, 4, 12 }, 4);
    demo(new int[] { 10 }, new int[] { 2, 3, 4, 12 }, 4);
    demo(new int[] { 10 }, new int[] { 2, 3, 4, 12 }, 10);
    demo(new int[] { }, new int[] { 2, 3, 4, 12 }, 10);
    demo(new int[] { 10 }, new int[] { }, 10);
    demo(new int[] { }, new int[] { }, 10);
  }

  public static void demo(int[] first, int[] second, int lim) {
    final List<Integer> l1 = IntStream.of(first).boxed().collect(Collectors.toList());
    final List<Integer> l2 = IntStream.of(second).boxed().collect(Collectors.toList());
    System.out.println("Merge of " + lim + " element(s) in " + l1 + " and " + l2 + " is " +
        lowerBoundMerge(l1, l2, lim));
  }

  public static List<Integer> lowerBoundMerge(List<Integer> first, List<Integer> second, int lim) {
    // FIXME: arguments check

    final List<Integer> result = new ArrayList<>(lim);

    for (int i = 0, p1 = 0, p2 = 0; i < lim; ++i) {
      if (p1 < first.size()) {
        if (p2 < second.size()) {
          final int e1 = first.get(p1);
          final int e2 = second.get(p2);

          if (e1 < e2) {
            result.add(first.get(p1));
            ++p1;
          } else {
            result.add(second.get(p2));
            ++p2;
          }

          continue;
        }

        // second list exhausted, get remaining elements from the first list
        result.add(first.get(p1));
        ++p1;
        continue;
      } else if (p2 >= second.size()) {
        // FIXME: alt flow - error might be thrown (lim is too big, none of given lists have that many elements)
        break; // both first and second lists exhausted
      }

      // first list exhausted, get element from the second one
      result.add(second.get(p2));
      ++p2;
    }

    return result;
  }
}
