package problems.leet100.challenge528.w1;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/528/week-1/3285/
 * <p>
 * Given an integer array nums, find the contiguous subarray (containing at least one number) which has the largest sum and return its sum.
 *
 * Example:
 *
 * Input: [-2,1,-3,4,-1,2,1,-5,4],
 * Output: 6
 * Explanation: [4,-1,2,1] has the largest sum = 6.
 * Follow up:
 *
 * If you have figured out the O(n) solution, try coding another solution using the divide and conquer approach, which is more subtle.
 * </p>
 */
public class MaximumSubarraySolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println("sum = " + maxSubArray(new int[] { -2,1,-3,4,-1,2,1,-5,4 }));
    }
  }

  private static int maxSubArray(int[] nums) {
    int maxPrev = nums[0];
    int maxSum = maxPrev;
    for (int i = 1; i < nums.length; ++i) {
      final int nextCombined = maxPrev + nums[i];
      maxPrev = Math.max(nums[i], nextCombined);
      maxSum = Math.max(maxSum, maxPrev);
    }
    return maxSum;
  }
}
