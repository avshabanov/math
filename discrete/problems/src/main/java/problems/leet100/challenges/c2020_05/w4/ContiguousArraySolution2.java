package problems.leet100.challenges.c2020_05.w4;

import java.util.HashMap;
import java.util.Map;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/537/week-4-may-22nd-may-28th/3341/
 * <p>Given a binary array, find the maximum length of a contiguous subarray with equal number of 0 and 1.</p>
 * <p>Note: The length of the given binary array will not exceed 50,000.</p>
 */
public class ContiguousArraySolution2 { /* second, more elegant solution of the same problem */

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println(findMaxLength(new int[]{0,1}));
      System.out.println(findMaxLength(new int[]{0,1,0}));
      System.out.println(findMaxLength(new int[]{1,1,0,0,0,0,1,1,1,1,1,1,1}));
    }
  }

  private static int findMaxLength(int[] nums) {
    final Map<Integer, Integer> m = new HashMap<>(nums.length * 2);
    m.put(0, 0);
    int prev = 0;
    int max = 0;
    for (int i = 0; i <= nums.length; ++i) {
      final Integer other = m.get(prev);
      max = (other != null ? Math.max(max, i - other) : max);

      prev = prev + (i < nums.length ? (nums[i] == 0 ? -1 : 1) : 0);

      final Integer val = i + 1;
      m.putIfAbsent(prev, val);
    }
    return max;
  }
}
