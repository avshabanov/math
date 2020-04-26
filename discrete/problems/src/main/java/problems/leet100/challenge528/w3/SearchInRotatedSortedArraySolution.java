package problems.leet100.challenge528.w3;

import java.util.Arrays;

/**
 * https://leetcode.com/explore/challenge/card/30-day-leetcoding-challenge/530/week-3/3304/
 * <p>Suppose an array sorted in ascending order is rotated at some pivot unknown to you beforehand.
 *
 * (i.e., [0,1,2,4,5,6,7] might become [4,5,6,7,0,1,2]).
 *
 * You are given a target value to search. If found in the array return its index, otherwise return -1.
 *
 * You may assume no duplicate exists in the array.
 *
 * Your algorithm's runtime complexity must be in the order of O(log n).</p>
 */
public class SearchInRotatedSortedArraySolution {

  public static void main(String[] args) {
    demo(new int[]{0, 1, 2}, 1);
    demo(new int[]{2, 0, 1}, 0);
    demo(new int[]{2, 0, 1}, 1);
    demo(new int[]{2, 0, 1}, 2);
    demo(new int[]{4,5,6,7,0,1,2}, 3);
    demo(new int[]{4,5,6,7,0,1,2}, 7);
  }

  private static void demo(int[] arr, int target) {
    System.out.printf("Input: arr=%s, target=%d\nOutput: %d\n", Arrays.toString(arr), target, search(arr, target));
  }

  private static int search(int[] nums, int target) {
    if (nums.length == 0) {
      return -1;
    }

    // find rotation index in `start`
    int start = 0;
    int end = nums.length - 1;
    while (nums[start] > nums[end]) {
      final int delta = (end - start) / 2;
      final int median = end - delta;
      if (nums[start] > nums[median]) {
        end = median;
      } else {
        start = median;
      }
      if (delta == 0) {
        start = end;
      }
    }

    // offset will hold start position of the array
    final int offset = start;

    // perform binary search in rotated array
    start = 0;
    end = nums.length - 1;
    while (start <= end) {
      final int median = end - (end - start) / 2;
      final int medianPos = (offset + median) % nums.length;
      if (nums[medianPos] == target) {
        return medianPos;
      }
      if (start == end) {
        break;
      }
      if (nums[medianPos] > target) {
        end = median - 1;
      } else {
        start = median + 1;
      }
    }

    return -1;
  }
}
