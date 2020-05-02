package problems.leet100.challenges.c2020_04.w4;

import java.util.HashMap;
import java.util.Map;

/**
 * https://leetcode.com/explore/challenge/card/30-day-leetcoding-challenge/531/week-4/3307/
 * <p>Given an array of integers and an integer k, you need to find the total number of continuous subarrays whose sum
 * equals to k.</p>
 */
public class SubarraySumEqualsNumSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.printf("Output: %d\n", subarraySum(new int[]{1, 1, 1}, 2));
      System.out.printf("Output: %d\n", subarraySum(new int[]{1, 2, 3, 4, 2, 1, 0}, 7));
    }
  }

  private static int subarraySum(int[] nums, int k) {
    int result = 0;

    final Map<Integer, Integer> sumFrequences = new HashMap<>();
    for (int sum = 0, i = 0; i < nums.length; ++i) {
      sum += nums[i];

      final int addend = sum  - k;
      final Integer freq = sumFrequences.get(addend);
      if (freq != null) {
        result += freq;
      }

      if (addend == 0) {
        result += 1;
      }

      sumFrequences.compute(sum, (ignored, v) -> v == null ? 1 : 1 + v);
    }

    return result;
  }
}
