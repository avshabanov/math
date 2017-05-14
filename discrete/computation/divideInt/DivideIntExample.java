/**
 * Taken from https://leetcode.com/problems/divide-two-integers/#/description
 *
 * Divide two integers without using multiplication, division and mod operator.
 * If it is overflow, return MAX_INT.
 */
public final class DivideIntExample {

  public static void main(String[] args) {
    demo(4, 1);
    demo(9, 3);
    demo(-9, 3);
    demo(-9, -4);
    demo(-37, 14);
    demo(1635468795, 11);
    demo(-264548798, 37);
    demo(Integer.MIN_VALUE, -2);
  }

  private static void demo(int dividend, int divisor) {
    final int actual = divide(dividend, divisor);
    final int expected = dividend / divisor;
    final String passMarker = actual == expected ? "OK" : "FAIL";
    System.out.printf("[%s] %d / %d = %d, actual = %d\n", passMarker, dividend, divisor, expected, actual);
  }

  private static int divide(int dividend, int divisor) {
    if (divisor == 0) {
      return Integer.MAX_VALUE;
    }

    if (divisor == Integer.MIN_VALUE) {
      return dividend == Integer.MIN_VALUE ? 1 : 0;
    }

    if (dividend == Integer.MIN_VALUE && divisor == -1) {
      return Integer.MAX_VALUE; // overflow
    }

    // extract result sign and make divisor and dividend positive
    int sign = 1; //=Math.sign(dividend) * Math.sign(divisor) <-- not used due to constraints above
    long longDivisor = divisor;
    long longDividend = dividend;
    if (dividend < 0) {
      longDividend = -longDividend;
      if (divisor < 0) {
        longDivisor = -longDivisor;
      } else {
        sign = -1;
      }
    } else {
      if (divisor < 0) {
        longDivisor = -longDivisor;
        sign = -1;
      }
    }

    // compare normalized values
    if (longDividend < longDivisor) {
      return 0;
    }

    final int shifts = Long.numberOfLeadingZeros(longDivisor) - Long.numberOfLeadingZeros(longDividend);
    int bit = 1 << shifts;
    long divisorSub = longDivisor << shifts;
    long result = 0;
    do {
      if (divisorSub <= longDividend) {
        result |= bit;
        longDividend -= divisorSub;
      }
      bit = bit >> 1;
      divisorSub = divisorSub >> 1;
    } while (divisorSub > 0);

    return (int) (sign > 0 ? result : -result);
  }
}
