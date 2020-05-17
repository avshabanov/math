package problems.leet100.challenges.c2020_05.w2;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/535/week-2-may-8th-may-14th/3327/
 * <p>You are given a sorted array consisting of only integers where every element appears exactly twice,
 * except for one element which appears exactly once. Find this single element that appears only once.</p>
 * <p>Note: Your solution should run in O(log n) time and O(1) space.</p>
 */
public class SingleElementInSortedArraySolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println(singleNonDuplicate(new int[]{1,1,2,3,3,4,4,8,8}));
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      System.out.println(singleNonDuplicate(new int[]{3,3,7,7,10,11,11}));
    }
  }

  public static final class Demo3 {
    public static void main(String[] args) {
      System.out.println(singleNonDuplicate(new int[]{11}));
      //System.out.println(singleNonDuplicate(new int[]{1,2,2,3,3}));
    }
  }

  private static int singleNonDuplicate(int[] nums) {
    int left = 0;
    int right = nums.length;
    while (left < right) {
      int medium = (left + right) / 2;
      int elem = nums[medium];
      if (medium > left && elem == nums[medium - 1]) {
        if ((medium - left - 1) % 2 == 0) {
          left = medium + 1;
        } else {
          right = medium - 1;
        }
      } else if ((medium + 1) < right && elem == nums[medium + 1]) {
        if ((medium - left) % 2 == 0) {
          left = medium + 2;
        } else {
          right = medium;
        }
      } else {
        return elem;
      }
    }
    return -1;
  }
}
