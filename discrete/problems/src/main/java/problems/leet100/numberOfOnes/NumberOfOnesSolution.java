package problems.leet100.numberOfOnes;

/**
 * https://leetcode.com/problems/number-of-digit-one/
 * <p>Given an integer n, count the total number of digit 1 appearing in all
 * non-negative integers less than or equal to n.</p>
 */
public class NumberOfOnesSolution {

  public static void main(String[] args) {
    demo(13);
    demo(2103);
    demo(99);
    demo(20);
    demo(200);
    demo(2000);
    demo(999);
    demo(3000);
    demo(9999);
  }

  private static void demo(int top) {
    int nums = 0;
    for (int i = 1; i <= top; ++i) {
      final String s = Integer.toString(i);
      for (int j = 0; j < s.length(); ++j) {
        if (s.charAt(j) == '1') {
          ++nums;
        }
      }
    }
    final int nums2 = countDigitOne(top);
    System.out.printf("For tops=%d, nums(1)=%d, nums2(1)=%d\n", top, nums, nums2);
  }

  private static int countDigitOne(final int n) {
    int result = 0;
    int rem = 0;
    for (int k = n, m = 1, p = 0; k > 0; k = k / 10, m = m * 10, ++p) {
      final int digit = k % 10;
      if (digit == 0) {
        continue;
      }

      final int num = digit * m;

      final int ones;
      final int prev = p > 0 ? NUM_OF_ONES[p - 1] : 0;
      if (digit > 1) {
        ones = m + prev * digit;
      } else {
        ones = 1 + rem + prev;
      }

      result += ones;

      rem += num;
    }
    return result;
  }

  private static final int INT_MAX_LOG10 = (int) Math.log10(Integer.MAX_VALUE);
  private static final int[] NUM_OF_ONES = new int[INT_MAX_LOG10];
  static {
    int prev = 1;
    for (int i = 0; i < NUM_OF_ONES.length; ++i) {
      NUM_OF_ONES[i] = prev * (i + 1);
      prev = prev * 10;
    }
  }
}
