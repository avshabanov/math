package problems.leet100.challenges.c2020_05.w4;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/537/week-4-may-22nd-may-28th/3338/
 * <p>Given two lists of closed intervals, each list of intervals is pairwise disjoint and in sorted order.
 *
 * Return the intersection of these two interval lists.
 *
 * (Formally, a closed interval [a, b] (with a <= b) denotes the set of real numbers x with a <= x <= b.
 * The intersection of two closed intervals is a set of real numbers that is either empty, or can be represented
 * as a closed interval.  For example, the intersection of [1, 3] and [2, 4] is [2, 3].)</p>
 */
public class IntervalListIntersectionsSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      final int[][] a = {{0,2},{5,10},{13,23},{24,25}};
      final int[][] b = {{1,5},{8,12},{15,24},{25,26}};
      final int[][] result = intervalIntersection(a, b);
      System.out.println(Arrays.stream(result).map(Arrays::toString).collect(Collectors.joining(", ")));
    }
  }

  private static int[][] intervalIntersection(int[][] a, int[][] b) {
    final List<int[]> intervals = new ArrayList<>();
    for (int aPos = 0, bPos = 0; aPos < a.length && bPos < b.length;) {
      final int[] ai = a[aPos];
      final int[] bi = b[bPos];
      if (ai[0] <= bi[1] && ai[1] >= bi[0]) {
        intervals.add(new int[]{Math.max(ai[0], bi[0]), Math.min(ai[1], bi[1])});
      }

      if (bi[1] > ai[1]) {
        ++aPos;
      } else {
        ++bPos;
      }
    }

    return intervals.toArray(new int[intervals.size()][]);
  }
}
