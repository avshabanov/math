package problems.leet100.challenges.c2020_04.w2;

import java.util.Arrays;
import java.util.OptionalInt;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/529/week-2/3298/
 * <p>Given a binary array, find the maximum length of a contiguous subarray with equal number of 0 and 1.</p>
 * <p>Note: The length of the given binary array will not exceed 50,000.</p>
 */
public class ContiguousArraySolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(OptionalInt.of(4), 0,1,1,0,1,1,1,0);
      demo(OptionalInt.of(10), 0,1,1,0,1,1,1,0,0,0);
      demo(OptionalInt.of(14), 0,0,0,0,0,0,1,0,1,0,0,1,1,0,0,0,0,1,1,1,0);
      demo(OptionalInt.of(16), 0,1,0,1,0,0,1,1,0,0,0,0,1,1,1,1);
      demo(OptionalInt.of(14), 0,1,0,1,0,0,1,1,0,0,0,0,1,1,1,0);
      demo(OptionalInt.of(2), 0,1);
      demo(OptionalInt.of(2), 0,1,0);
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      demo(OptionalInt.of(4), 0,1,1,0,1,1,1,0);
    }
  }

  @SuppressWarnings("OptionalUsedAsFieldOrParameterType")
  private static void demo(OptionalInt expected, int... nums) {
    final int l = findMaxLength(nums);
    expected.ifPresent(n -> {
      if (n != l) {
        throw new AssertionError("expected=" + n + " got=" + l + " for " + Arrays.toString(nums));
      }
    });
    System.out.printf("Input: %s\nOutput: %d\n", Arrays.toString(nums), l);
  }

  private static int findMaxLength(int[] nums) {
    return findMaxLength1(nums);
  }

  /*
  n:  0, 1, 1, 0, 1, 1, 1, 0
  0:  0, 3, 7
  1:  1, 2, 4, 5, 6
  b:  0, 1, 2, 1, 2, 3, 4, 3

   */
  private static int findMaxLength1(int[] nums) {
    //System.out.printf("---\n[DBG] Nums=%s\n", Arrays.toString(nums));

    // step 1: find size of balance indices array based on the traits of the input array. It can be as small as two.
    int bottom = 0;
    int top = 0;
    int prev = 0;
    for (int num : nums) {
      final int cur = prev + (num == 0 ? -1 : 1);
      bottom = Math.min(bottom, cur);
      top = Math.max(top, cur);
      prev = cur;
    }

    int maxLength = 0;
    final int[] balanceIndices = new int[top - bottom + 1];
    Arrays.fill(balanceIndices, -1);
    prev = -bottom;
    for (int i = 0; i < nums.length; ++i) {
      if (balanceIndices[prev] < 0) {
        balanceIndices[prev] = i; // reachable by this number
      }

      final int next = prev + (nums[i] == 0 ? -1 : 1);
      prev = next;
      final int predIndex = balanceIndices[next];
      if (predIndex < 0) {
        continue;
      }

      final int newLength = i - predIndex + 1;
      maxLength = Math.max(maxLength, newLength);
    }

    //System.out.printf("[DBG] balanceIndices=%s\n", Arrays.toString(balanceIndices));

    return maxLength;
  }

  private static int findMaxLength2(int[] nums) {
    int[][] positions = { new int[nums.length], new int[nums.length] };
    int[] counts = { 0, 0 };
    int maxSubsequentLength = 0;
    int nextSubsequentLength = 1;

    for (int i = 0; i < nums.length; ++i) {
      final int n = nums[i];
      if (n < 0 || n > 1) {
        throw new IllegalArgumentException("Non binary value: nums[" + i + "]=" + n);
      }

      positions[n][counts[n]] = i;
      ++counts[n];

      while (nextSubsequentLength <= Math.min(counts[0], counts[1])) {
        // now verify, that previous subsequence fits equal number of zeros and ones
        final int s0 = positions[0][counts[0] - nextSubsequentLength];
        final int s1 = positions[1][counts[1] - nextSubsequentLength];

        // if s0 > s1 then pred(s1) < s0
        // if s1 > s0 then pred(s0) < s1
        final int pred0 = counts[0] > nextSubsequentLength ? positions[0][counts[0] - nextSubsequentLength - 1] : -1;
        final int pred1 = counts[1] > nextSubsequentLength ? positions[1][counts[1] - nextSubsequentLength - 1] : -1;

        if ((s0 > s1 && s1 > pred0) ||
            (s1 > s0 && s0 > pred1)) {
          // ok
          maxSubsequentLength = nextSubsequentLength;
          ++nextSubsequentLength;
        } else {
          break;
        }
      }
    }

    return 2 * maxSubsequentLength;
  }
}
