package problems.leet100.firstMissingPositive;

import java.util.Arrays;

/**
 * 41. First Missing Positive
 * https://leetcode.com/problems/first-missing-positive/
 * <p>Given an unsorted integer array, find the smallest missing positive integer.</p>
 * <p>
 * Example 1:
 * Input: [1,2,0]
 * Output: 3
 *
 * Example 2:
 * Input: [3,4,-1,1]
 * Output: 2
 *
 * Example 3:
 * Input: [7,8,9,11,12]
 * Output: 1
 * </p>
 * <p>
 * Note:
 * Your algorithm should run in O(n) time and use constant extra space.
 * </p>
 */
public class FirstMissingPositiveSolution {

  public static void main(String[] args) {
    demo(1, 3, 5, 7, 11, 13, 14, 12, 10, 8, 6, 4, 2);
    demo(1, 2, 3, 10, 11, 12, 7, 6, 5, 4);
    demo(3, 4, -1, 1);
    demo(7, 8, 9, 11, 12);
    demo(1, 2, 0);
  }

  private static void demo(int... nums) {
    final String numsStr = Arrays.toString(nums);
    int n = firstMissingPositive(nums);
    int n2 = firstMissingPositiveInplace(nums);
    if (n != n2) {
      throw new AssertionError("Mismatch for " + numsStr + " expected=" + n + ", actual=" + n2);
    }
    System.out.printf("Input: %s\nOutput: %d\n\n", numsStr, n);
  }

  // solution 1: use O(1) memory, but modify nums in place
  private static int firstMissingPositiveInplace(int[] nums) {
    for (int n : nums) {
      while (n > 0 && n <= nums.length) {
        final int index = n - 1;
        final int tmp = nums[index];
        if (tmp == n) {
          break; // ignore duplicates
        }
        nums[index] = n;
        n = tmp;
      }
    }

    for (int i = 0; i < nums.length; ++i) {
      final int target = i + 1;
      if (nums[i] != target) {
        return target;
      }
    }

    return nums.length + 1;
  }

  // solution 1: use O(n) memory (worst case), but don't modify nums in place
  private static int firstMissingPositive(int[] nums) {
    // optimization: allocate only countPositives number, disregard negative numbers
    int countPositives = 0;
    int minPositive = Integer.MAX_VALUE;
    for (final int n : nums) {
      if (n <= 0) {
        continue;
      }

      ++countPositives;
      minPositive = Math.min(n, minPositive);
    }

    // shortcut: positive range doesn't have `one`, no need to look further
    if (minPositive > 1) {
      return 1;
    }

    final int[] copyNums = new int[countPositives];
    for (final int n : nums) {
      if (n <= 0 || n > countPositives) {
        continue;
      }
      copyNums[n - 1] = n;
    }

    for (int i = 0; i < countPositives; ++i) {
      final int target = i + 1;
      if (copyNums[i] != target) {
        return target;
      }
    }
    return countPositives + 1;
  }
}
