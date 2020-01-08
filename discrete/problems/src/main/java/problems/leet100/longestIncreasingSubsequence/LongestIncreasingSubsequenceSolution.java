package problems.leet100.longestIncreasingSubsequence;

import java.util.Arrays;
import java.util.stream.IntStream;

/**
 * 300. Longest Increasing Subsequence
 * https://leetcode.com/problems/longest-increasing-subsequence/
 *
 * <p>Given an unsorted array of integers, find the length of longest increasing subsequence.
 *
 * Example:
 *
 * Input: [10,9,2,5,3,7,101,18]
 * Output: 4
 * Explanation: The longest increasing subsequence is [2,3,7,101], therefore the length is 4.
 *
 * Note:
 *
 * There may be more than one LIS combination, it is only necessary for you to return the length.
 * Your algorithm should run in O(n2) complexity.
 * Follow up: Could you improve it to O(n log n) time complexity?</p>
 *
 * Submission details:
 * <p>Runtime: 4 ms, faster than 73.59% of Java online submissions for Longest Increasing Subsequence.
 * Memory Usage: 36.9 MB, less than 40.00% of Java online submissions for Longest Increasing Subsequence.</p>
 */
public class LongestIncreasingSubsequenceSolution {

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

    final Solver solver = new Solver(nums);
    for (int nextTryPos = 0; nextTryPos >= 0;) {
      nextTryPos = solver.maxSequence(nextTryPos, 1);
    }

    return solver.maxLength;
  }

  private static final class Solver {
    final int[] nums;
    int maxLength;

    Solver(int[] nums) {
      this.nums = nums;
    }

    int maxSequence(final int pos, final int subsequenceSize) {
      int nextTryPos = -1;
      int current = this.nums[pos];
      for (int i = pos + 1;; ++i) {
        final int bound = Math.min(this.nums.length, this.nums.length + subsequenceSize - this.maxLength);
        if (i >= bound) {
          break;
        }

        final int other = this.nums[i];
        if (other > current) {
          maxSequence(i, subsequenceSize + 1);
          continue;
        } else if (other == current) {
          continue; // skip non-increasing elements
        }

        if (nextTryPos < 0) {
          nextTryPos = i;
        }
      }

      // at this point we have subsequenceSize
      this.maxLength = Math.max(this.maxLength, subsequenceSize);

      return nextTryPos;
    }
  }
}
