package problems.leet100.challenges.c2020_06.w2;

import java.util.Arrays;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/540/week-2-june-8th-june-14th/3357/
 * <p>Given an array with n objects colored red, white or blue, sort them in-place so that objects of the same color
 * are adjacent, with the colors in the order red, white and blue.
 *
 * Here, we will use the integers 0, 1, and 2 to represent the color red, white, and blue respectively.
 *
 * Note: You are not suppose to use the library's sort function for this problem.
 *
 * Example:
 *
 * Input: [2,0,2,1,1,0]
 * Output: [0,0,1,1,2,2]
 * Follow up:
 *
 * A rather straight forward solution is a two-pass algorithm using counting sort.
 * First, iterate the array counting number of 0's, 1's, and 2's, then overwrite array with total number of 0's,
 * then 1's and followed by 2's.
 * Could you come up with a one-pass algorithm using only constant space?</p>
 */
public class SortColors {

  public static void main(String[] args) {
    final int[] nums = {2, 1, 2, 0, 0, 1};
    InPlace.sortColors(nums);
    System.out.println(Arrays.toString(nums));
  }

  private static void sortColors(int[] nums) {
    final int[] stats = new int[3];
    for (int n : nums) {
      ++stats[n];
    }
    int pos = 0;
    for (int u = 0; u < stats.length; ++u) {
      for (int i = 0; i < stats[u]; ++i) {
        nums[pos] = u;
        ++pos;
      }
    }
  }

  private static final class InPlace {
    static void sortColors(int[] nums) {
      int oneStartPos = 0;
      int twoTrailingPos = nums.length;

      // skip zeroes
      while (oneStartPos < nums.length && nums[oneStartPos] == 0) {
        ++oneStartPos;
      }

      // sort within 'ones' section putting number to the intended position
      for (int i = oneStartPos; i < twoTrailingPos; ) {
        if (nums[i] == 1) {
          ++i;
          continue;
        }

        if (nums[i] == 0) {
          swap(nums, oneStartPos, i);
          ++oneStartPos;
          ++i;
          continue;
        }

        --twoTrailingPos;
        swap(nums, twoTrailingPos, i);
      }
    }

    static void swap(int[] nums, int index1, int index2) {
      final int temp = nums[index1];
      nums[index1] = nums[index2];
      nums[index2] = temp;
    }
  }
}
