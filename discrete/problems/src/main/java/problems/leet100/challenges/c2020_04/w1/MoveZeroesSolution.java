package problems.leet100.challenges.c2020_04.w1;

import java.util.Arrays;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/528/week-1/3286/
 * <p>
 * Given an array nums, write a function to move all 0's to the end of it while maintaining the relative order of
 * the non-zero elements.
 *
 * Example:
 *
 * Input: [0,1,0,3,12]
 * Output: [1,3,12,0,0]
 * Note:
 *
 * You must do this in-place without making a copy of the array.
 * Minimize the total number of operations.
 * </p>
 */
public class MoveZeroesSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(0);
      demo(1);
      demo(0,1,0,3,12);
    }
  }

  private static void demo(int... nums) {
    final String src = Arrays.toString(nums);
    moveZeroes(nums);
    System.out.printf("Input: %s\nOutput: %s\n", src, Arrays.toString(nums));
  }

  private static void moveZeroes(int[] nums) {
    int lastZeroIdx = nums.length - 1;
    while (lastZeroIdx >= 0) {
      if (nums[lastZeroIdx] == 0) {
        --lastZeroIdx;
      } else {
        break;
      }
    }

    if (lastZeroIdx < 0) {
      return; // all zeroes
    }

    int startPos = 0;
    for (int i = 0; i <= lastZeroIdx; ++i) {
      if (nums[i] == 0) {
        continue;
      }

      nums[startPos] = nums[i];
      ++startPos;
    }

    while (startPos <= lastZeroIdx) {
      nums[startPos] = 0;
      ++startPos;
    }
  }
}
