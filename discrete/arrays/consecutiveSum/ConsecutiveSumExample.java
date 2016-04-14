import java.util.Arrays;

/**
 * Sample run:
 * <pre>
 * Consecutive sum to 1 in [1] is [1]
 * Consecutive sum to 2 in [1, 2] is [2]
 * Consecutive sum to 3 in [1, 2] is [1, 2]
 * Consecutive sum to 4 in [1, 2] is <none>
 * Consecutive sum to 5 in [1, 3, 5, 7, 9] is [5]
 * Consecutive sum to 6 in [1, 3, 5, 7, 9] is <none>
 * Consecutive sum to 73 in [1, 3, 5, 7, 9] is <none>
 * Consecutive sum to 8 in [1, 3, 5, 7, 9] is [3, 5]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class ConsecutiveSumExample {

  public static void main(String[] args) {
    demo(new int[] {1}, 1);
    demo(new int[] {1, 2}, 2);
    demo(new int[] {1, 2}, 3);
    demo(new int[] {1, 2}, 4);
    demo(new int[] {1, 3, 5, 7, 9}, 5);
    demo(new int[] {1, 3, 5, 7, 9}, 6);
    demo(new int[] {1, 3, 5, 7, 9}, 73);
    demo(new int[] {1, 3, 5, 7, 9}, 8);
  }

  public static void demo(int[] arr, int k) {
    final int[] consecutiveSum = getConsecutiveSum(arr, k);
    System.out.println("Consecutive sum to " + k + " in " + Arrays.toString(arr) + " is " +
        (consecutiveSum == null ? "<none>" : Arrays.toString(consecutiveSum)));
  }

  public static int[] getConsecutiveSum(int[] arr, int k) {
    for (int i = 0; i < arr.length; ++i) {
      int sum = 0;
      for (int j = i; j < arr.length; ++j) {
        final int e = arr[j];
        if (e < 0) {
          throw new IllegalArgumentException("Negative element in arr=" + Arrays.toString(arr) + " at position=" + j);
        }

        sum += e;
        if (sum == k) {
          return Arrays.copyOfRange(arr, i, j + 1);
        } else if (sum > k) {
          break;
        }
      }
    }

    return null;
  }
}
