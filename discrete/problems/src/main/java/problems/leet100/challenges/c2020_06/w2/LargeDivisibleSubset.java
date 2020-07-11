package problems.leet100.challenges.c2020_06.w2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/540/week-2-june-8th-june-14th/3359/
 * <p>Given a set of distinct positive integers, find the largest subset such that every pair (Si, Sj) of
 * elements in this subset satisfies:
 *
 * Si % Sj = 0 or Sj % Si = 0.
 *
 * If there are multiple solutions, return any subset is fine.
 *
 * Example 1:
 *
 * Input: [1,2,3]
 * Output: [1,2] (of course, [1,3] will also be ok)
 * Example 2:
 *
 * Input: [1,2,4,8]
 * Output: [1,2,4,8]</p>
 */
public class LargeDivisibleSubset {

  public static void main(String[] args) {
    System.out.println(largestDivisibleSubset(new int[] {1,2,4,8}));
    System.out.println(largestDivisibleSubset(new int[] {1,3,4,7,8,11,16}));
  }

  private static List<Integer> largestDivisibleSubset(int[] nums) {
    if (nums.length == 0) {
      return Collections.emptyList();
    }
    Arrays.sort(nums);
    final int[] dp = new int[nums.length]; //< divisors count
    Arrays.fill(dp, 1);

    final int[] prev = new int[nums.length]; //< previous divisor indices
    Arrays.fill(prev, -1);

    int max = 0;
    for (int i = 1; i < nums.length; ++i) {
      for (int j = 0; j < i; ++j) {
        if (nums[i] % nums[j] == 0 && dp[i] < dp[j] + 1) {
          dp[i] = dp[j] + 1;
          prev[i] = j;
        }
      }
      if (dp[max] < dp[i]) {
        max = i;
      }
    }

    final List<Integer> result = new ArrayList<>();
    for (int i = max; i >= 0;) {
      result.add(nums[i]);
      i = prev[i];
    }
    return result;
  }
}
