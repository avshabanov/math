package problems.leet100.challenges.cmisc;

import java.util.NavigableMap;
import java.util.NavigableSet;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * 132 Pattern
 * Given an array of n integers nums, a 132 pattern is a subsequence of three integers
 * nums[i], nums[j] and nums[k] such that i < j < k and nums[i] < nums[k] < nums[j].
 *
 * Return true if there is a 132 pattern in nums, otherwise, return false.
 *
 * Follow up: The O(n^2) is trivial, could you come up with the O(n logn) or the O(n) solution?
 */
public class Find123Pattern {

  private static boolean find132pattern(int[] nums) {
    // put up a map of all number-to-freq, runtime = O(n*log(n))
    final NavigableMap<Integer, Integer> m = new TreeMap<>();
    for (final int n : nums) {
      m.compute(n, (ignored, c) -> 1 + (c == null ? 0 : c));
    }

    // test for elements presence, runtime = O(n*log(n))
    final NavigableSet<Integer> prior = new TreeSet<>();
    for (final int n : nums) {
      m.compute(n, (ignored, c) -> c == null || c <= 1 ? null : (c - 1));
      prior.add(n);

      final Integer nextLowerKey = m.lowerKey(n);
      if (nextLowerKey == null) {
        continue;
      }

      final Integer prevUpperKey = prior.lower(nextLowerKey);
      if (prevUpperKey != null && prevUpperKey < n) {
        return true;
      }
    }

    return false;
  }

  public static void main(String[] args) {
    System.out.println(find132pattern(new int[]{-1,3,2,0}));
    System.out.println(find132pattern(new int[]{-2, 1, 1}));
  }
}
