package problems.leet100.jumpGameII;

import java.util.Arrays;

/**
 * 45. Jump Game II
 * https://leetcode.com/problems/jump-game-ii/
 *
 * <p>
 * Given an array of non-negative integers, you are initially positioned at the first index of the array.
 * Each element in the array represents your maximum jump length at that position.
 * Your goal is to reach the last index in the minimum number of jumps.
 * </p>
 * <p>
 * Example:
 * Input: [2,3,1,1,4]
 * Output: 2
 *
 * Explanation: The minimum number of jumps to reach the last index is 2.
 *     Jump 1 step from index 0 to 1, then 3 steps to the last index.
 * Note:
 * You can assume that you can always reach the last index.
 * </p>
 */
public class JumpGameIISolution {

  public static void main(String[] args) {
    demo(new int[]{1});
    demo(new int[]{2, 3, 1, 1, 4});
  }

  private static void demo(int[] nums) {
    final int numJumps = jump(nums);
    System.out.printf("Input: %s\nOutput: %d\n---\n",
        Arrays.toString(nums), numJumps);
  }

  private static int jump(int[] nums) {
    if (nums.length == 0) {
      throw new IllegalArgumentException("nums should not be empty");
    }

    final int[] dp = new int[nums.length];
    for (int i = 1; i < nums.length; ++i) {
      dp[i] = Integer.MAX_VALUE;
    }

    for (int i = 0; i < nums.length - 1; ++i) {
      // cur number is holding the minimum number of jumps one can make to arrive to this index
      final int reachJumpCount = dp[i] + 1;
      final int reachPos = Math.min(nums.length, i + nums[i] + 1);
      for (int j = i + 1; j < reachPos; ++j) {
        dp[j] = Math.min(dp[j], reachJumpCount);
      }
    }

    return dp[nums.length - 1];
  }
}
