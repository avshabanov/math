package problems.arrays.median2;

import java.util.Arrays;

/**
 * Solution for "Median of Two Sorted Arrays" problem - https://leetcode.com/problems/median-of-two-sorted-arrays/
 * This takes a non-optimal, brute-force approach to the problem.
 * <code>
 *    Runtime: 44 ms, faster than 29.60% of Java online submissions for Median of Two Sorted Arrays.
 *    Memory Usage: 38.9 MB, less than 15.69% of Java online submissions for Median of Two Sorted Arrays.
 * </code>
 */
public class MedianOfTwoSortedArraysViaMerge {

  private static double findMedianSortedArrays(int[] nums1, int[] nums2) {
    final int[] c = merge(nums1, nums2);

    final double median;
    if (c.length % 2 == 0) {
      final int twinPos = c.length / 2;
      median = (c[twinPos - 1] + c[twinPos]) / 2.0;
    } else {
      median = c[c.length / 2];
    }
    return median;
  }

  private static int[] merge(int[] nums1, int[] nums2) {
    final int[] c = new int[nums1.length + nums2.length];
    for (int i1 = 0, i2 = 0, i = 0;; ++i) {
      if (i1 < nums1.length) {
        if (i2 < nums2.length) {
          // we have elements in both num1 and num2
          final int e1 = nums1[i1];
          final int e2 = nums2[i2];
          if (e1 < e2) {
            // take element from the first array
            c[i] = e1;
            ++i1;
          } else {
            // take element from the second array
            c[i] = e2;
            ++i2;
          }
        } else {
          // we have elements in num1 only
          System.arraycopy(nums1, i1, c, i, (nums1.length - i1));
          break;
        }
      } else if (i2 < nums2.length) {
        // we have elements in num2 only
        System.arraycopy(nums2, i2, c, i, (nums2.length - i2));
        break;
      } else {
        // no more elements
        break;
      }
    }
    return c;
  }

  //
  // Demo
  //

  private static void printMerged(int[] nums1, int[] nums2) {
    Arrays.sort(nums1);
    Arrays.sort(nums2);
    System.out.println(String.format("Merge(%s, %s)=%s", Arrays.toString(nums1), Arrays.toString(nums2),
        Arrays.toString(merge(nums1, nums2))));
  }

  private static void printMedian(int[] nums1, int[] nums2) {
    Arrays.sort(nums1);
    Arrays.sort(nums2);
    System.out.println("nums1 = " + Arrays.toString(nums1));
    System.out.println("nums2 = " + Arrays.toString(nums2));
    System.out.println("The median is " + findMedianSortedArrays(nums1, nums2));
    System.out.println();
  }

  public static final class Demo1 {
    public static void main(String[] args) {
      printMerged(new int[]{}, new int[]{});
      printMerged(new int[]{1, 3}, new int[]{});
      printMerged(new int[]{}, new int[]{2});
      printMerged(new int[]{}, new int[]{2, 3});
      printMerged(new int[]{1, 3}, new int[]{2});
      printMerged(new int[]{2}, new int[]{1, 3});
      printMerged(new int[]{2, 4}, new int[]{1, 3});
      printMerged(new int[]{1, 3}, new int[]{2, 4});
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      printMedian(new int[]{1, 3}, new int[]{2});
      printMedian(new int[]{1, 2}, new int[]{3, 4});
      printMedian(new int[]{}, new int[]{2, 3});
    }
  }
}
