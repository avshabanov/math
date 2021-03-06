import util.SortUtil;

import java.util.Arrays;

/**
 * Illustration on how to implement insertion sort,
 * see also https://en.wikipedia.org/wiki/Insertion_sort
 */
public class InsertionSort {
  public static void main(String[] args) {
    SortUtil.runStandardFixture(InsertionSort::insertionSort);
  }

  private static void insertionSort(int[] arr) {
    for (int i = 0; i < arr.length; ++i) {
      int elem = arr[i];

      // find place to insert given element into
      int insertionIndex = i;
      for (int j = i - 1; j >= 0; --j) {
        if (elem >= arr[j]) {
          break;
        }
        insertionIndex = j;
      }

      // move elements to put inserted element into
      if (insertionIndex < i) {
        //noinspection ManualArrayCopy
        for (int j = i; j > insertionIndex; --j) {
          arr[j] = arr[j - 1];
        }
        arr[insertionIndex] = elem;
        System.out.println("  [INSERTION] arr=" + Arrays.toString(arr));
      }
    }
  }
}
