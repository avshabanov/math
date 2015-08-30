import java.util.Arrays;

public class MergeSort {

  public static void main(String[] args) {
    SortUtil.runStandardFixture(new SortUtil.InplaceSortAlgorithm() {
      @Override
      public void sort(int[] arr) {
        inplaceMergeSort(arr);
      }
    });
  }



  private static void inplaceMergeSort(int[] arr) {
    bottomUpSort(arr, Arrays.copyOf(arr, arr.length), arr.length);
  }

  //
  // Helpers
  //

  private static void bottomUpSort(int[] arr, int[] tmp, int n) {
    for (int width = 1; width < n; width *= 2) {
      final int doubleWidth = 2 * width;
      for (int i = 0; i < n; i += doubleWidth) {
        bottomUpMerge(arr, i, Math.min(i + width, n), Math.min(i + doubleWidth, n), tmp);
      }
      System.arraycopy(tmp, 0, arr, 0, tmp.length);

      System.out.println("  [MERGE_PASS] arr=" + Arrays.toString(arr));
    }
  }

  private static void bottomUpMerge(int[] arr, int left, int right, int end, int[] tmp) {
    int i0 = left;
    int i1 = right;

    for (int j = left; j < end; ++j) {
      if (i0 < right && (i1 >= end || arr[i0] <= arr[i1])) {
        tmp[j] = arr[i0];
        i0 += 1;
      } else {
        tmp[j] = arr[i1];
        i1 += 1;
      }
    }
  }
}
