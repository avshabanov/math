package problems.leet100.largestRectangleInHistogram;

import java.util.*;

/**
 * 84. Largest Rectangle in Histogram
 * https://leetcode.com/problems/largest-rectangle-in-histogram/
 * <p>Given n non-negative integers representing the histogram's bar height where the width of each bar is 1,
 * find the area of largest rectangle in the histogram.</p>
 * Submission details:
 * <p>Runtime: 9 ms, faster than 78.36% of Java online submissions for Largest Rectangle in Histogram.
 * Memory Usage: 39.7 MB, less than 100.00% of Java online submissions for Largest Rectangle in Histogram.
 * </p>
 */
public class LargestRectangleInHistogramSolution {

  public static void main(String[] args) {
    demo(new int[]{9,0});
    demo(new int[]{0});
    demo(new int[]{});
    demo(new int[]{1,1});
    demo(new int[]{2,1,2});
    demo(new int[]{1,2,3,4,5,6,7});
    demo(new int[]{2,1,5,6,2,3});
  }

  private static void demo(int[] heights) {
    System.out.printf(
        "Largest rect area in hist=%s is %d\n",
        Arrays.toString(heights),
        largestRectangleArea(heights)
    );
  }

  private static int largestRectangleArea(int[] heights) {
    if (heights.length == 0) {
      return 0;
    }

    // tracks largest rectangle area found so far
    int largestArea = 0;

    // tracks rectangle states
    final RectState[] rectStates = new RectState[heights.length];
    int rectStateLength = 0;

    for (int i = 0; i <= heights.length; ++i) {
      final int height;
      if (i == heights.length) {
        // special end-of-sequence case to trigger reevaluation of the previously inserted rect states
        height = 0;
      } else {
        height = heights[i];
      }

      final RectState newRectState = new RectState(height, i);

      // complete all the rects for previous (taller) histogram elements that have been added before
      final int tailPosition = Arrays.binarySearch(rectStates, 0, rectStateLength, newRectState);
      final int cullingPosition = tailPosition < 0 ? (-tailPosition - 1) : tailPosition + 1;
      for (int j = cullingPosition; j < rectStateLength; ++j) {
        final RectState rectState = rectStates[j];
        final int width = i - rectState.startPosition;
        final int rectArea = width * rectState.height;

        // re-evaluate the area largest rect that has been tracked so far
        largestArea = Math.max(largestArea, rectArea);

        // bigger rects may "vanish" for their height is above the current one, but smaller rects that can be fitted in
        // shall still be tracked, and so in order to do that we can reuse new rect state by extending its width as
        // far as possible to the left
        newRectState.startPosition = Math.min(newRectState.startPosition, rectState.startPosition);
      }

      if (height <= 0) {
        // reset the length and don't insert zero or negative-height histogram elements
        rectStateLength = 0;
        continue;
      }

      // add new rect state and update current length, culling all the rects above it
      rectStates[cullingPosition] = newRectState;
      rectStateLength = cullingPosition + 1;
    }

    return largestArea;
  }

  private static final class RectState implements Comparable<RectState> {
    final int height;

    /**
     * Tracks start position (corresponding histogram entry) of this rect.
     * This field is not final to allow dynamic extension during culling of the rects corresponding to the
     * taller histogram elements.
     */
    /*final*/ int startPosition;

    RectState(int height, int startPosition) {
      this.height = height;
      this.startPosition = startPosition;
    }

    @Override
    public int compareTo(RectState o) {
      return Integer.compare(this.height, o.height);
    }
  }
}
