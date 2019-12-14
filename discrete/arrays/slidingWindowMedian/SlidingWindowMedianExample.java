import java.util.Arrays;
import java.util.function.IntToDoubleFunction;

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
 *
 * Submission details (as of 2019-12-13):
 * <pre>
 * Runtime: 15 ms, faster than 98.33% of Java online submissions for Sliding Window Median.
 * Memory Usage: 44.4 MB, less than 20.00% of Java online submissions for Sliding Window Median.
 * </pre>
 *
 * Possible optimizations:
 * <ul>
 *   <li>Remove tail element allocation for sliding window (would safe a 10-100 nsec / call)</li>
 *   <li>Use min and max heaps for tracking median element</li>
 * </ul>
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

    private static final class WindowItem implements Comparable<WindowItem> {
      private int val;
      private WindowItem next;

      WindowItem(int v) {
        this.val = v;
      }

      @Override
      public String toString() {
        return Integer.toString(val);
      }

      @Override
      public int compareTo(WindowItem o) {
        return Integer.compare(val, o.val);
      }
    }

    private static final class WindowedMedianExtractor implements MedianExtractor {
      private final int[] source;
      private int srcPos;

      // in-line data structure that unites linked list and array,
      // we need array traits for sorting, and linked list for queueing next index,
      // which is going to be a position of the sliding window
      private final WindowItem[] window;
      private WindowItem head;
      private WindowItem tail;
      private final IntToDoubleFunction medianExtractor;

      WindowedMedianExtractor(int[] source, int k) {
        this.source = source;

        this.window = new WindowItem[k];
        WindowItem cursor = null;
        for (int i = 0; i < k; ++i) {
          final WindowItem windowItem = new WindowItem(source[i]);
          if (cursor == null) {
            head = windowItem;
          } else {
            cursor.next = windowItem;
          }
          cursor = windowItem;
          this.window[i] = windowItem;
        }
        this.tail = cursor;

        this.srcPos = k - 1;

        Arrays.sort(window);

        if (this.window.length % 2 == 0) {
          medianExtractor = rightIndexPos -> {
            final int leftIndexPos = rightIndexPos - 1;
            return ((double) window[leftIndexPos].val + window[rightIndexPos].val) / 2.0;
          };
        } else {
          medianExtractor = rightIndexPos -> window[rightIndexPos].val;
        }
      }

      @Override
      public boolean hasNext() {
        return srcPos < source.length;
      }

      @Override
      public double next() {
        final double median = medianExtractor.applyAsDouble(this.window.length / 2);
        srcPos = srcPos + 1;

        if (srcPos >= source.length) {
          return median;
        }

        if (window.length == 1) {
          // shortcut for small windows
          window[0].val = source[srcPos];
          return median;
        }

        final int headPos = Arrays.binarySearch(window, head);
        if (headPos < 0) {
          throw new IllegalStateException("Invariant check failed: (headPos=" + headPos + ")< 0");
        }

        // make element that head points to a new tail
        final WindowItem newTail = new WindowItem(source[srcPos]);
        head = head.next;
        tail.next = newTail;
        tail = newTail;

        // readjust elements to retain sorted trait of the window array
        int newTailPos = Arrays.binarySearch(window, newTail);
        if (newTailPos < 0) {
          newTailPos = -newTailPos - 1;
        }

        // now shift elements in the proper order
        if (headPos > newTailPos) {
          // shift left-to-right
          System.arraycopy(window, newTailPos, window, newTailPos + 1, headPos - newTailPos);
        } else if (headPos < newTailPos) {
          // shift right-to-left
          newTailPos = newTailPos - 1;
          System.arraycopy(window, headPos + 1, window, headPos, newTailPos - headPos);
        } // else -> no need to move array slice

        window[newTailPos] = newTail;

        return median;
      }
    }
  }
}
