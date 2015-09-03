import java.util.Arrays;

/**
 * @author Alexander Shabanov
 */
public class SortedTranspositionExample {

  public static void main(String[] args) {
    int[] arr = splitArray(new int[]{1, 2, 3, 4, 5, 6, 7, 8}, 2);
    int index = getBoundIndex(arr);
    System.out.println("arr=" + Arrays.toString(arr) + ", index=" + index);

    arr = splitArray(new int[]{1, 2, 3, 4, 5, 6, 7, 8}, 5);
    index = getBoundIndex(arr);
    System.out.println("arr=" + Arrays.toString(arr) + ", index=" + index);
  }

  private static int getBoundIndex(int[] arr) {
    int left = 0;
    int right = arr.length - 1;
    for (;;) {
      if ((right - left) < 2) {
        return right;
      }
      assert arr[left] >= arr[right];

      final int median = (left + right) / 2;
      final int element = arr[median];
      if (arr[left] <= element) {
        left = median;
      } else {
        right = median;
      }
    }
  }

  private static int[] splitArray(int[] arr, int splitIndex) {
    final int[] temp = Arrays.copyOfRange(arr, 0, splitIndex);
    System.arraycopy(arr, splitIndex, arr, 0, arr.length - splitIndex);
    System.arraycopy(temp, 0, arr, arr.length - splitIndex, temp.length);
    return arr;
  }
}
