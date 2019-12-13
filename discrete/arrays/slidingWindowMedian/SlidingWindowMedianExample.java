import java.util.Arrays;
import java.util.Comparator;

/**
 * Solution for sliding window median problem:
 * https://leetcode.com/problems/sliding-window-median
 *
 * Problem description:
 * <pre>
 * Median is the middle value in an ordered integer list. If the size of the list is even, there is no middle value.
 * So the median is the mean of the two middle value.
 *
 * Examples:
 * [2,3,4] , the median is 3
 *
 * [2,3], the median is (2 + 3) / 2 = 2.5
 *
 * Given an array nums, there is a sliding window of size k which is moving from the very left of the array to the
 * very right. You can only see the k numbers in the window.
 * Each time the sliding window moves right by one position.
 * Your job is to output the median array for each window in the original array.
 *
 * For example,
 * Given nums = [1,3,-1,-3,5,3,6,7], and k = 3.
 *
 * Window position                Median
 * ---------------               -----
 * [1  3  -1] -3  5  3  6  7       1
 *  1 [3  -1  -3] 5  3  6  7       -1
 *  1  3 [-1  -3  5] 3  6  7       -1
 *  1  3  -1 [-3  5  3] 6  7       3
 *  1  3  -1  -3 [5  3  6] 7       5
 *  1  3  -1  -3  5 [3  6  7]      6
 * Therefore, return the median sliding window as [1,-1,-1,3,5,6].
 *
 * Note:
 * You may assume k is always valid, ie: k is always smaller than input array's size for non-empty array.
 * </pre>
 */
public class SlidingWindowMedianExample {
  public static void main(String[] args) {
    demo(new int[]{1,3,-1,-3,5,3,6,7}, 3);
    demo(new int[]{1,2,3}, 1);
  }

  private static void demo(int[] nums, int k) {
    System.out.printf(
        "Sliding window of array %s and size %d is %s\n",
        Arrays.toString(nums),
        k,
        Arrays.toString(new Solution().medianSlidingWindow(nums, k))
    );
  }

  private static final class Solution {
    public double[] medianSlidingWindow(int[] nums, int k) {
      final int len = nums.length - k;
      if (len < 0) {
        return new double[0];
      }

      final double[] medians = new double[len + 1];
      MedianExtractor e = new WindowedMedianExtractor(nums, k);
      for (int i = 0; e.hasNext();) {
        medians[i++] = e.next();
      }

      return medians;
    }

    private interface MedianExtractor {
      double next();
      boolean hasNext();
    }

    private static final class Index {
      private int pos;
      private Index next;

      Index(int pos) {
        this.pos = pos;
      }

      @Override
      public String toString() {
        return "#(" + pos + ')';
      }
    }

    private static final class WindowedMedianExtractor implements MedianExtractor, Comparator<Index> {
      private final int[] source;
      private int srcPos;

      // in-line data structure that unites linked list and array,
      // we need array traits for sorting, and linked list for queueing next index,
      // which is going to be a position of the sliding window
      private final Index[] indices;
      private Index head;
      private Index tail;

      WindowedMedianExtractor(int[] source, int k) {
        this.source = source;

        this.indices = new Index[k];
        Index cursor = null;
        for (int i = 0; i < k; ++i) {
          final Index index = new Index(i);
          if (cursor == null) {
            head = index;
          } else {
            cursor.next = index;
          }
          cursor = index;
          this.indices[i] = index;
        }
        this.tail = cursor;

        this.srcPos = k - 1;

        // TODO: use binary search
        sortIndices();
      }

      @Override
      public boolean hasNext() {
        return srcPos < source.length;
      }

      @Override
      public double next() {
        //System.out.printf("[DBG] indices=%s\n", Arrays.toString(indices));
        final int rightIndexPos = this.indices.length / 2;
        final double median;
        if (this.indices.length % 2 == 0) {
          final int leftIndexPos = rightIndexPos - 1;
          median = ((double) source[indices[leftIndexPos].pos] + source[indices[rightIndexPos].pos]) / 2.0;
        } else {
          median = source[indices[rightIndexPos].pos];
        }

        srcPos = srcPos + 1;

        if (srcPos >= source.length) {
          return median;
        }

        final Index newTail = head;
        // check, that list has at least two elements
        if (head != tail) {
          head = head.next;
          tail.next = newTail;
          tail = newTail;
        }

        newTail.pos = srcPos;
        newTail.next = null;

        sortIndices();

        return median;
      }

      @Override
      public int compare(Index leftIndex, Index rightIndex) {
        return Integer.compare(source[leftIndex.pos], source[rightIndex.pos]);
      }

      private void sortIndices() {
        Arrays.sort(indices, this);
      }
    }
  }
}
