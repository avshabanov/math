package problems.leet100.challenges.c2020_04.w4;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/531/week-4/3308/
 * <p>Given a range [m, n] where 0 <= m <= n <= 2147483647, return the bitwise AND of all numbers in this range,
 * inclusive.</p>
 */
public class BitwiseAndRangeSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.printf("mb0=%d\n", rangeBitwiseAnd(5, 5));
      System.out.printf("mb1=%d\n", rangeBitwiseAnd(200, 257));
      System.out.printf("mb2=%d\n", rangeBitwiseAnd(5, 7));
      System.out.printf("mb3=%d\n", rangeBitwiseAnd(1024 - 5, 1024 - 2));
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      System.out.printf("mb1=%d\n", rangeBitwiseAndBruteForce(200, 257));
      System.out.printf("mb2=%d\n", rangeBitwiseAndBruteForce(5, 7));
      System.out.printf("mb3=%d\n", rangeBitwiseAndBruteForce(1024 - 5, 1024 - 2));
    }
  }

  private static int rangeBitwiseAnd(int m, int n) {
    int maxBitM = Integer.highestOneBit(m);
    int maxBitN = Integer.highestOneBit(n);
    if (maxBitM != maxBitN) {
      return 0;
    }

    int result = maxBitM;
    while (maxBitM > 0) {
      maxBitM = maxBitM >> 1;
      maxBitN = maxBitN >> 1;

      final int bit = m & maxBitM;
      if (bit != (n & maxBitN)) {
        break;
      }

      result |= bit;
    }
    return result;
  }

  private static int rangeBitwiseAndBruteForce(int m, int n) {
    int result = m;
    for (m = m + 1; m <= n; ++m) {
      result = result & m;
    }
    return result;
  }
}
