package problems.leet100.challenge528.w3;

import java.util.Arrays;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/530/week-3/3300/
 * <p>Given an array nums of n integers where n > 1,  return an array output such that output[i] is equal to the
 * product of all the elements of nums except nums[i].</p>
 * <p>Constraint: It's guaranteed that the product of the elements of any prefix or suffix of the array (including the
 * whole array) fits in a 32 bit integer.
 *
 * Note: Please solve it without division and in O(n).
 *
 * Follow up:
 * Could you solve it with constant space complexity? (The output array does not count as extra space for the purpose of
 * space complexity analysis.)</p>
 */
public class ProductOfArrayExceptSelf {

  public static void main(String[] args) {
    demo(1,2,3,4);
    demo(5,6,7,8,9);
  }

  private static void demo(int... nums) {
    final int[] resultExpected = productExceptSelfCheat(nums);
    final int[] result = productExceptSelf(nums);
    if (!Arrays.equals(resultExpected, result)) {
      throw new AssertionError("For nums=" + Arrays.toString(nums) +
          " expected=" + Arrays.toString(resultExpected) + ", actual=" + Arrays.toString(result));
    }
    System.out.printf("Input: %s\nOutput: %s\n---\n", Arrays.toString(nums), Arrays.toString(result));
  }

  /*
  Possible solutions:

  1. Use logarithm and exponent (multiplication = addition, division = substraction when using log(nums[i]))
  2. Implement division using shifts/subtractions
  3. Partitioned product
   */
  private static int[] productExceptSelf(int[] nums) {
    final int[] result = new int[nums.length];
    Arrays.fill(result, 1);
    partitionedProduct(nums, result, 0, nums.length);
    return result;
  }

  private static void partitionedProduct(int[] nums, int[] result, int from, int to) {
    if ((from + 1) >= to) {
      return;
    }

    // transfer product of the first half of the array chunk to the right
    final int median = (from + to) / 2;
    int product = 1;
    for (int i = from; i < median; ++i) {
      product *= nums[i];
    }
    for (int i = median; i < to; ++i) {
      result[i] *= product;
    }

    // transfer product of the second half of the array chunk to the left
    product = 1;
    for (int i = median; i < to; ++i) {
      product *= nums[i];
    }
    for (int i = from; i < median; ++i) {
      result[i] *= product;
    }

    partitionedProduct(nums, result, from, median);
    partitionedProduct(nums, result, median, to);
  }

  // brute force solution using forbidden division operation
  private static int[] productExceptSelfCheat(int[] nums) {
    final int[] result = new int[nums.length];
    int product = 1;
    for (final int num : nums) {
      if (num < 1) {
        throw new IllegalArgumentException();
      }
      product *= num;
    }
    for (int i = 0; i < nums.length; ++i) {
      result[i] = product / nums[i];
    }
    return result;
  }
}
