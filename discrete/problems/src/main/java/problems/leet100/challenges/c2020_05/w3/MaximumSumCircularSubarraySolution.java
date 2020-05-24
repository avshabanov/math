package problems.leet100.challenges.c2020_05.w3;

import java.util.PriorityQueue;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/536/week-3-may-15th-may-21st/3330/
 * <p>Given a circular array C of integers represented by A, find the maximum possible sum of a non-empty subarray of C.
 *
 * Here, a circular array means the end of the array connects to the beginning of the array.
 * (Formally, C[i] = A[i] when 0 <= i < A.length, and C[i+A.length] = C[i] when i >= 0.)
 *
 * Also, a subarray may only include each element of the fixed buffer A at most once.
 * (Formally, for a subarray C[i], C[i+1], ..., C[j], there does not exist i <= k1, k2 <= j
 * with k1 % A.length = k2 % A.length.)</p>
 * <p>Note:
 * -30000 <= A[i] <= 30000
 * 1 <= A.length <= 30000</p>
 */
public class MaximumSumCircularSubarraySolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println(maxSubarraySumCircular(new int[] {1, -1, 2}));
      System.out.println(maxSubarraySumCircular(new int[] {1, 2}));
      System.out.println(maxSubarraySumCircular(new int[] {1}));
    }
  }

  private static int maxSubarraySumCircular(int[] arr) {
    if (arr.length == 0) {
      return 0;
    }

    final PriorityQueue<SumElement> queue = new PriorityQueue<>();
    queue.add(new SumElement(0, 0));
    int maxSum = arr[0];
    int previousSum = maxSum;
    final int length = arr.length * 2;
    for (int i = 1; i < length; ++i) {
      queue.add(new SumElement(i, previousSum));

      SumElement min = queue.peek();
      while ((i - min.pos) >= arr.length) {
        queue.poll();
        min = queue.peek();
      }

      final int newSum = previousSum + arr[i % arr.length];
      final int candidateSum = newSum - min.sum;
      maxSum = Math.max(candidateSum, maxSum);

      previousSum = newSum;
    }

    return maxSum;
  }

  private static final class SumElement implements Comparable<SumElement> {
    final int pos;
    final int sum;

    public SumElement(int pos, int sum) {
      this.pos = pos;
      this.sum = sum;
    }

    @Override public int compareTo(SumElement o) {
      int result = Integer.compare(sum, o.sum);
      return result == 0 ? Integer.compare(pos, o.pos) : result;
    }
  }
}
