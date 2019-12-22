package problems.leet100.majorityElement;

import java.util.Arrays;

/**
 * 169. Majority Element
 * <p>Given an array of size n, find the majority element.
 * The majority element is the element that appears more than ⌊ n/2 ⌋ times.
 * You may assume that the array is non-empty and the majority element always exist in the array.</p>
 */
public class MajorityElementSolution {
  public static void main(String[] args) {
    demo(new int[]{-1, 1, 1, 1, 2, 1});
    demo(new int[]{3, 2, 3});
    demo(new int[]{3, 3, 4});
    demo(new int[]{2, 2, 1, 1, 1, 2, 2});
  }

  private static void demo(int[] arr) {
    System.out.println("Majority element in " + Arrays.toString(arr) + " is " + majorityElement(arr));
  }

  private static int majorityElement(int[] nums) {
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
