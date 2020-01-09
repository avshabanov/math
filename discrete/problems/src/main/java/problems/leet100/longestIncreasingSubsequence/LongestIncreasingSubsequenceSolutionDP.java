package problems.leet100.longestIncreasingSubsequence;

import java.util.Arrays;
import java.util.stream.IntStream;

/**
 * Solution for 'longest increasing subsequence' problem in dynamic programming style.
 */
public class LongestIncreasingSubsequenceSolutionDP {

  public static void main(String[] args) {
    demo(10,9,2,5,3,4);
    demo(2);
    demo(1, 2);
    demo(2, 1);
    demo(10,9,2,5,3,7,101,18);
    demo(IntStream.range(0, 2500).toArray());
    demo(IntStream.range(0, 2500).map(n -> 2500 - n).toArray());
  }

  private static void demo(int... nums) {
    System.out.printf("For nums=%s\n\tlen(lis)=%d\n", Arrays.toString(nums), lengthOfLIS(nums));
  }

  private static int lengthOfLIS(int[] nums) {
    if (nums.length == 0) {
      return 0;
    }

    int maxFound = 1;
    final int last = nums.length - 1;
    final int[] reach = new int[nums.length];
    Arrays.fill(reach, 1);
    for (int i = 0; i < last; ++i) {
      int quantity = reach[i];
      final int current = nums[i];
      final int nextQuantity = quantity + 1;
      for (int j = i + 1; j < nums.length; ++j) {
        final int next = nums[j];
        if (next > current) {
          reach[j] = Math.max(nextQuantity, reach[j]);
          maxFound = Math.max(maxFound, nextQuantity);
        }
      }
    }
    return maxFound;
  }
}
