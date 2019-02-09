package problems.arrays.median2;

import java.util.Arrays;

/**
 * Solution for "Median of Two Sorted Arrays" problem - https://leetcode.com/problems/median-of-two-sorted-arrays/
 * <code>
 *    Runtime: 24 ms, faster than 99.85% of Java online submissions for Median of Two Sorted Arrays.
 *    Memory Usage: 38.8 MB, less than 16.00% of Java online submissions for Median of Two Sorted Arrays.
 * </code>
 */
public class MedianOfTwoSortedArraysViaSelectivePick {

  private static double findMedianSortedArrays(int[] nums1, int[] nums2) {
    final int totalLength = nums1.length + nums2.length;
    final int lastPos = totalLength / 2;
    final int triggerPos = totalLength % 2 == 0 ? lastPos - 1 : lastPos;
    double result = 0;

    for (int i1 = 0, i2 = 0, i = 0; i <= lastPos; ++i) {
      double e;

      if (i1 < nums1.length) {
        if (i2 < nums2.length) {
          // we have elements in both num1 and num2
          final int e1 = nums1[i1];
          final int e2 = nums2[i2];
          if (e1 < e2) {
            // take element from the first array
            e = e1;
            ++i1;
          } else {
            // take element from the second array
            e = e2;
            ++i2;
          }
        } else {
          // we have elements in num1 only
          e = nums1[i1];
          ++i1;
        }
      } else if (i2 < nums2.length) {
        // we have elements in num2 only
        e = nums2[i2];
        ++i2;
      } else {
        // no more elements - should never happen
        break;
      }

      if (i >= triggerPos) {
        result += e;
      }
    }

    return result / (1 + lastPos - triggerPos);
  }

  //
  // Demo
  //

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
      printMedian(new int[]{1, 3}, new int[]{2});
      printMedian(new int[]{1, 2}, new int[]{3, 4});
      printMedian(new int[]{}, new int[]{2, 3});
    }
  }
}
