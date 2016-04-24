import java.util.Arrays;

/**
 * Sample run:
 * <pre>
 * Biggest subarray in [] is []
 * Biggest subarray in [1] is [1]
 * Biggest subarray in [1, 2, -1, 3, -1] is [1, 2, -1, 3]
 * Biggest subarray in [1, 2, -10, 3, 1] is [3, 1]
 * Biggest subarray in [1, 2, 2, -10, 3, 1] is [1, 2, 2]
 * Biggest subarray in [-2, 5, -1, 7, -3] is [5, -1, 7]
 * </pre>
 * 
 * @author Alexander Shabanov
 */
public final class BiggestSumExample {

  public static void main(String[] args) {
    demo(new int[0]);
    demo(new int[] { 1 });
    demo(new int[] { 1, 2, -1, 3, -1 });
    demo(new int[] { 1, 2, -10, 3, 1 });
    demo(new int[] { 1, 2, 2, -10, 3, 1 });
    demo(new int[] { -2, 5, -1, 7, -3 });
  }

  public static void demo(int[] arr) {
    System.out.println("Biggest subarray in " + Arrays.toString(arr) + " is " +
        Arrays.toString(getSubarrayWithBiggestSum(arr)));
  }

  public static int[] getSubarrayWithBiggestSum(int[] arr) {
    int from = 0;
    int to = 0;
    int sum = 0;

    for (int i = 0; i < arr.length; ++i) {
      int subarraySum = 0;
      for (int j = i; j < arr.length; ++j) {
        subarraySum += arr[j];
        if ((subarraySum > sum) || (to == from)) {
          sum = subarraySum;
          from = i;
          to = j + 1;
        }
      }
    }

    return Arrays.copyOfRange(arr, from, to);
  }
}
