package problems.leet100.challenges.c2020_04.w4;

import java.util.Arrays;
import java.util.BitSet;
import java.util.function.Function;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/531/week-4/3310/
 * <p>Given an array of non-negative integers, you are initially positioned at the first index of the array.
 *
 * Each element in the array represents your maximum jump length at that position.
 *
 * Determine if you are able to reach the last index.</p>
 */
public class JumpGameSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(2,3,1,1,4);
      demo(3,2,1,0,4);
    }
  }

  private static void demo(int... nums) {
    Function<int[], Boolean> f = Greedy::canJump;
    if (Boolean.parseBoolean(System.getProperty("USE_DP"))) {
      f = DP::canJump;
    }
    System.out.printf("Input: %s\nOutput: %s\n", Arrays.toString(nums), f.apply(nums));
  }

  private static final class Greedy {
    private static boolean canJump(int[] nums) {
      if (nums == null || nums.length <= 1) {
        return true;
      }

      int maxReachIndex = 0;
      for (int i = 0; i < nums.length; ++i) {
        if (i > maxReachIndex) {
          return false;
        }
        maxReachIndex = Math.max(maxReachIndex, Math.min(nums.length, nums[i] + i));
      }
      return true;
    }
  }

  private static final class DP {
    private static boolean canJump(int[] nums) {
      if (nums == null || nums.length <= 1) {
        return true;
      }
      final BitSet dp = new BitSet(nums.length);
      dp.set(0);
      for (int i = 0; i < nums.length; ++i) {
        if (!dp.get(i)) {
          return false;
        }
        final int toIndex = Math.min(nums.length, i + 1 + nums[i]);
        dp.set(i, toIndex);
      }

      return dp.get(nums.length - 1);
    }
  }
}
