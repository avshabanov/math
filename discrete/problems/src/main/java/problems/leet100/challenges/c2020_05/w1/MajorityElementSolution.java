package problems.leet100.challenges.c2020_05.w1;

import java.util.Arrays;

/**
 * https://leetcode.com/explore/featured/card/may-leetcoding-challenge/534/week-1-may-1st-may-7th/3321/
 * <p>Given an array of size n, find the majority element. The majority element is the element that
 * appears more than ⌊ n/2 ⌋ times.
 *
 * You may assume that the array is non-empty and the majority element always exist in the array.</p>
 */
public class MajorityElementSolution {

  private static final class Mine {
    private static int majorityElement(int[] nums) {
      if (nums.length == 0) {
        throw new IllegalArgumentException("Empty array");
      }

      if (nums.length == 1) {
        return nums[0];
      }

      Arrays.sort(nums);
      final int median = nums.length / 2;
      if (nums[0] == nums[median]) {
        return nums[0];
      }
      return nums[median];
    }
  }

  private static final class Leaked {
    public int majorityElement(int[] nums) {
      if (nums.length == 0) {
        throw new IllegalArgumentException("Can't find majority element in the empty array");
      }

      if (nums.length == 1) {
        return nums[0];
      }

      Arrays.sort(nums);

      final int leftBound;
      final int rightBound;
      if (nums.length % 2 == 0) {
        leftBound = nums.length / 2;
        rightBound = leftBound - 1;
      } else {
        leftBound = rightBound = nums.length / 2;
      }

      if (nums[0] == nums[leftBound]) {
        return nums[0];
      }
      if (nums[nums.length - 1] == nums[rightBound]) {
        return nums[nums.length - 1];
      }

      // last case - assuming that element is always there, it should be on either left or right bound
      assert nums[leftBound] == nums[rightBound];
      return nums[leftBound];
    }
  }
}
