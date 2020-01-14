package problems.leet100.mergeIntervals;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

/**
 * 56. Merge Intervals
 * https://leetcode.com/problems/merge-intervals/
 *
 * <p>Given a collection of intervals, merge all overlapping intervals.</p>
 */
public class MergeIntervalsSolution {

  public static void main(String[] args) {
    demo(new int[][]{new int[]{3, 4}, new int[]{5, 6}, new int[]{1, 2}});
    demo(new int[][]{new int[]{1, 5}, new int[]{3, 4}, new int[]{2, 7}});
    demo(new int[][]{new int[]{5, 9}, new int[]{1, 2}, new int[]{3, 7}});
  }

  private static void demo(int[][] intervals) {
    final String originalIntervals = toString(intervals);
    final int[][] mergeResult = merge(intervals);
    System.out.printf(
        "Intervals %s merged to %s\n",
        originalIntervals,
        toString(mergeResult)
    );
  }

  private static String toString(int[][] intervals) {
    final List<String> intervalParts = Arrays.stream(intervals)
        .map(n -> String.format("[%d, %d]", n[0], n[1]))
        .collect(Collectors.toList());
    return intervalParts.toString();
  }

  private static int[][] merge(int[][] intervals) {
    Arrays.sort(intervals, PairComparator.INSTANCE);
    List<int[]> result = new ArrayList<>();
    for (int i = 0; i < intervals.length; ++i) {
      // base
      int[] lhs = Arrays.copyOf(intervals[i], intervals[i].length);
      for (int j = i + 1; j < intervals.length; ++j) {
        final int[] rhs = intervals[j];
        if (rhs[0] > lhs[1]) {
          break;
        }
        lhs[1] = Math.max(lhs[1], rhs[1]);
        ++i;
      }
      result.add(lhs);
    }
    return result.toArray(new int[][]{});
  }

  private static final class PairComparator implements Comparator<int[]> {
    static final PairComparator INSTANCE = new PairComparator();

    @Override
    public int compare(int[] o1, int[] o2) {
      return Integer.compare(o1[0], o2[0]);
    }
  }
}

