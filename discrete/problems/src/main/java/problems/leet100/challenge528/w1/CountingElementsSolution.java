package problems.leet100.challenge528.w1;

import java.util.Arrays;
import java.util.BitSet;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/528/week-1/3289/
 *
 * <p>
 * Given an integer array arr, count element x such that x + 1 is also in arr.
 *
 * If there're duplicates in arr, count them separately.
 * </p>
 */
public class CountingElementsSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(1,2,3);
      demo(1,1,3,3,5,5,7,7);
      demo(1,3,2,3,5,0);
      demo(1,1,2,2);
    }
  }

  private static void demo(int... nums) {
    System.out.printf("Input: %s\nOutput: %d\n", Arrays.toString(nums), countElements(nums));
  }

  private static int countElements(int[] arr) {
    int max = arr[0];
    for (int i = 1; i < arr.length; ++i) {
      max = Math.max(arr[i], max);
    }
    final BitSet bs = new BitSet(max + 2);

    // 1st pass: add +1's
    for (int n : arr) {
      bs.set(n);
    }

    // 2nd pass: find which numbers are counted
    int counts = 0;
    for (int n : arr) {
      if (bs.get(n + 1)) {
        ++counts;
      }
    }

    return counts;
  }
}
