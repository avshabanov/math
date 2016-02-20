import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Sample output:
 * <pre>
 * Merging [(10->20), (40->50)] with [(25->35), (45->55)] : [(10->20), (25->35), (40->55)]
 * Merging [(1->2), (7->8)] with [(3->4), (5->6)] : [(1->2), (3->4), (5->6), (7->8)]
 * Merging [(1->2), (3->4)] with [(2->3), (4->5)] : [(1->5)]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class IntervalsMergeExample {

  public static void main(String[] args) {
    demo(Arrays.asList(r(10, 20), r(40, 50)), Arrays.asList(r(25, 35), r(45, 55)));
    demo(Arrays.asList(r(1, 2), r(7, 8)), Arrays.asList(r(3, 4), r(5, 6)));
    demo(Arrays.asList(r(1, 2), r(3, 4)), Arrays.asList(r(2, 3), r(4, 5)));
  }

  public static void demo(List<Range> arr1, List<Range> arr2) {
    System.out.println("Merging " + arr1 + " with " + arr2 + " : " + merge(arr1, arr2));
  }

  private static List<Range> merge(List<Range> arr1, List<Range> arr2) {
    if (arr1.isEmpty()) {
      return arr2;
    }

    final List<Range> result = new ArrayList<>();

    for (int i1 = 0, i2 = 0;;) {
      if (i1 >= arr1.size()) { // no more elements in the first array? ->
        addElements(result, arr2, i2);
        break; // add all the elements from second array and leave
      }

      if (i2 >= arr2.size()) { // no more elements in the second array? ->
        addElements(result, arr1, i1);
        break; // add all the elements from second array and leave
      }

      // merge elements from the first and second array
      final Range candidate = arr1.get(i1++).copy();
      for (;;) {
        while (i1 < arr1.size()) {
          final Range r1 = arr1.get(i1);
          if (r1.from > candidate.to) {
            break;
          }
          candidate.to = r1.to;
          ++i1;
        }

        // try merge element from the second array
        boolean merged = false;
        for (; i2 < arr2.size(); ++i2) {
          final Range r2 = arr2.get(i2);
          if (r2.to < candidate.from) {
            // given element precedes given range
            result.add(r2.copy());
            continue;
          }

          if (r2.from <= candidate.from && r2.to >= candidate.from) {
            // given element within the given range (merge from left)
            candidate.from = r2.from;
            candidate.to = Math.max(r2.to, candidate.to);
            merged = true;
            continue;
          }

          if (r2.from >= candidate.from && r2.from <= candidate.to) {
            // given element within the given range (merge from right)
            candidate.to = Math.max(r2.to, candidate.to);
            merged = true;
            continue;
          }

          break;
        }

        if (!merged) {
          result.add(candidate);
          break;
        }
      } // for - merge elements
    } // for - outer arrays

    return result;
  }

  private static void addElements(List<Range> result, List<Range> source, int startIndex) {
    for (; startIndex < source.size(); ++startIndex) {
      result.add(source.get(startIndex));
    }
  }

  private static Range r(int from, int to) {
    return new Range(from, to);
  }

  private static final class Range {
    int from;
    int to;

    public Range(Range range) {
      this(range.from, range.to);
    }

    public Range(int from, int to) {
      if (to < from) {
        throw new IllegalArgumentException("to=" + to + " is less than from=" + from);
      }
      this.from = from;
      this.to = to;
    }

    public Range copy() {
      return new Range(this);
    }

    @Override
    public String toString() {
      return "(" + from + "->" + to + ')';
    }
  }
}
