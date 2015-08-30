import java.util.Arrays;

public class LargeTranspositionSum {

  private static int[] getDecimalDigits(int num) {
    int arr[] = new int[12];
    int i = 0;

    for (; i < arr.length; ++i) {
      final int digit = num % 10;
      arr[i] = digit;

      num = num / 10;
      if (num == 0) {
        break;
      }
    }

    return Arrays.copyOfRange(arr, 0, i + 1);
  }

  private static int getMaxIntFromDigits(int[] digits) {
    final int[] d = Arrays.copyOf(digits, digits.length);
    Arrays.sort(d);
    int result = 0;
    for (int i = digits.length; i > 0; --i) {
      result = result * 10 + digits[i - 1];
    }
    return result;
  }

  public static void main(String[] args) {
    final int[] digits = getDecimalDigits(14560);
    Arrays.sort(digits);

    System.out.println("digits = " + Arrays.toString(digits) +
        ", maxNum = " + getMaxIntFromDigits(digits));
  }
}
