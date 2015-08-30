import java.util.Arrays;

public class QuickSort {
  public static void main(String[] args) {
    SortUtil.runStandardFixture(new SortUtil.InplaceSortAlgorithm() {
      @Override
      public void sort(int[] arr) {
        quickSort(arr);
      }
    });
  }

  private static void quickSort(int[] arr) {
    quickSortPart(arr, 0, arr.length - 1);
  }

  //
  // Helpers
  //

  private static void quickSortPart(int[] arr, int left, int right) {
    if (left < right) {
      int partitionIndex = partition(arr, left, right);
      quickSortPart(arr, left, partitionIndex - 1);
      quickSortPart(arr, partitionIndex + 1, right);
    }
  }

  private static int partition(int[] arr, int left, int right) {
    final int pivot = arr[right];
    int i = left;

    for (int j = left; j < right; ++j) {
      if (arr[j] < pivot) {
        final int temp = arr[i];
        arr[i] = arr[j];
        arr[j] = temp;
        i += 1;
      }
    }

    arr[right] = arr[i];
    arr[i] = pivot;

    System.out.println("  [PARTITION] left=" + left + ", right=" + right + ", pivot=" + pivot +
        ", partitionIndex=" + i + ", arr=" + Arrays.toString(arr));

    return i;
  }
}
