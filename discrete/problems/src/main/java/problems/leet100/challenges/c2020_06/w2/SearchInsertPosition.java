package problems.leet100.challenges.c2020_06.w2;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/540/week-2-june-8th-june-14th/3356/
 * <p>Given a sorted array and a target value, return the index if the target is found.
 * If not, return the index where it would be if it were inserted in order.
 * You may assume no duplicates in the array.</p>
 */
public class SearchInsertPosition {

  public static final class Demo1 {
    public static void main(String[] args) {
      final int[] n1 = {10, 20, 30, 40};
      System.out.println("P(n1, k1) = " + searchInsert(n1, 5));
      System.out.println("P(n1, k2) = " + searchInsert(n1, 15));
      System.out.println("P(n1, k3) = " + searchInsert(n1, 20));
      System.out.println("P(n1, k4) = " + searchInsert(n1, 25));
      System.out.println("P(n1, k5) = " + searchInsert(n1, 45));

      System.out.println("P(nil, c) = " + searchInsert(new int[0], 1));
    }
  }

  private static int searchInsert(int[] nums, int target) {
    int left = 0;
    for (int right = nums.length; left < right; ) {
      if (target <= nums[left]) {
        return left;
      }
      final int median = (left + right) / 2; // better: `right - (right - left) / 2` in case of a huge array
      if (target < nums[median]) {
        right = median;
        continue;
      }

      if (target > nums[median]) {
        left = median + 1;
        continue;
      }

      return median;
    }
    return left;
  }
}
