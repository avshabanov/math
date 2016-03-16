/**
 * Sample output:
 * <pre>
 * OK: value=0
 * OK: value=1
 * OK: value=-1
 * OK: value=-2147483648
 * OK: value=2147483647
 * OK: value=-1997
 * OK: value=2035
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class IntToStrExample {

  public static void main(String[] args) {
    demo(0);
    demo(1);
    demo(-1);
    demo(Integer.MIN_VALUE);
    demo(Integer.MAX_VALUE);
    demo(-1997);
    demo(2035);
  }

  public static void demo(int value) {
    final String expected = String.valueOf(value);
    final String actual = stringFromInt(value);
    if (!expected.equals(actual)) {
      throw new AssertionError("FAIL: mismatch for expected=" + expected + ", actual=" + actual);
    }

    System.out.println("OK: value=" + actual);
  }

  public static String stringFromInt(int value) {
    if (value == 0) {
      return "0";
    }

    // TODO: possible optimization: string builder size
    final StringBuilder sb = new StringBuilder(11); // 11 - size of decimal representation of the smallest 32-bit int
    final int sign = (value < 0 ? -1 : 1);

    while (value != 0) {
      final int digit = sign * (value % 10);
      sb.append((char) ('0' + digit));
      value = value / 10;
    }

    if (sign < 0) {
      sb.append('-');
    }

    sb.reverse();

    return sb.toString();
  }
}
