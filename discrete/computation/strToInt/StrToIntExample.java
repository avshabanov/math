/**
 * String-to-integer conversion, horrible java adaptation of new C++ standard's atoi.
 * See also https://leetcode.com/problems/string-to-integer-atoi/#/description
 * Passes tests as of 2017-05-10
 */
@SuppressWarnings("SpellCheckingInspection")
public class StrToIntExample {

  public static void main(String[] args) {
    demo("    -0012a42");
    demo("    +00045");
    demo("    010");
    demo("");
    demo("+-2");
    demo("0");
    demo("1");
    demo("-1");
    demo("-123");
  }

  public static void demo(String str) {
    System.out.printf("Converting string '%s' into number. Actual: %d\n", str, atoi(str));
  }

  private static int atoi(String str) {
    if (str.isEmpty()) {
      return 0; // consistent with C atoi
    }

    long result = 0;
    int sign = 1;
    boolean signMet = false;
    boolean digitMet = false;

    for (int i = 0; i < str.length(); ++i) {
      final char ch = str.charAt(i);
      if (ch == '-') {
        if (signMet || digitMet) {
          return 0;
        }
        sign = -1;
        signMet = true;
        continue;
      } else if (ch == '+') {
        if (signMet || digitMet) {
          return 0;
        }
        sign = 1;
        signMet = true;
        continue;
      }

      if (ch >= '0' && ch <= '9') {
        final int digit = ch - '0';
        result = (result * 10) + digit * sign;
        digitMet = true;

        if (result < Integer.MIN_VALUE) {
          return Integer.MIN_VALUE;
        } else if (result > Integer.MAX_VALUE) {
          return Integer.MAX_VALUE;
        }
      } else {
        if (digitMet || signMet) {
          // disregard unknown characters in the middle
          break;
        } else if (ch > ' ') {
          break;
        }
      }
    }

    return (int) result;
  }
}
