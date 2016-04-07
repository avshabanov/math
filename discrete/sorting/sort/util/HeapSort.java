package util;

import java.util.Arrays;

/**
 * Illustration of Heap Sort - https://en.wikipedia.org/wiki/Heapsort
 *
 * @author Alexander Shabanov
 */
public final class HeapSort {
  public static void main(String[] args) {
    SortUtil.runStandardFixture(HeapSort::heapSort);
  }

  private static void heapSort(int[] arr) {
    heapify(arr);

    int end = arr.length - 1;
    while (end > 0) {
      int tmp = arr[end];
      arr[end] = arr[0];
      arr[0] = tmp;

      end = end - 1;

      siftDown(arr, 0, end);
    }
  }

  //
  // Helpers
  //

  private static void heapify(int[] arr) {
    int start = (arr.length - 1) / 2;
    while (start >= 0) {
      siftDown(arr, start, arr.length - 1);
      start = start - 1;
    }
  }

  private static void siftDown(int[] arr, int start, int end) {
    int root = start;

    while ((root * 2 + 1) <= end) {
      int child = root * 2 + 1; // left child
      int swap = root; // child to swap with

      if (arr[swap] < arr[child]) {
        swap = child;
      }

      if ((child + 1) <= end && arr[swap] < arr[child + 1]) {
        swap = child + 1;
      }

      if (swap == root) {
        break; // the root holds the largest element
      } else {
        final int tmp = arr[root];
        arr[root] = arr[swap];
        arr[swap] = tmp;

        root = swap; // repeat to continue sifting down
      }
    }

    System.out.println("  [SIFT_DOWN] arr=" + Arrays.toString(arr));
  }
}
