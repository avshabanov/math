package problems.leet100.challenges.c2020_05.w2;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/535/week-2-may-8th-may-14th/3328/
 * <p>Given a non-negative integer num represented as a string, remove k digits from the number so that
 * the new number is the smallest possible.</p>
 * <p>Note:
 * The length of num is less than 10002 and will be ≥ k.
 * The given num does not contain any leading zero.</p>
 */
public class RemoveKDigitsSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println(removeKdigits("10200", 1));
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      System.out.println(removeKdigits("10", 2));
    }
  }

  public static final class Demo3 {
    public static void main(String[] args) {
      System.out.println(removeKdigits("1432219", 3));
    }
  }

  private static String removeKdigits(String num, int k) {
    final char[] buf = num.toCharArray();
    int length = buf.length;

    // repeat K times
    for (int i = 0; i < k; ++i) {
      // find and remove the digit to yield smallest number possible
      for (int pos = 0; pos < length; ++pos) {
        // remove either last digit or current digit if next one is smaller
        final int nextPos = pos + 1;
        if (nextPos < length && buf[pos] <= buf[nextPos]) {
          continue;
        }
        length = removeCharAt(buf, pos, length);
        break;
      }
    }

    return new String(buf, 0, length);
  }

  private static int removeCharAt(char[] buf, int pos, int length) {
    if (length == 1) {
      buf[0] = '0'; // if request is to remove last digit, use the smallest digit possible
      return length;
    }

    int newLength = length - 1;
    //noinspection ManualArrayCopy
    for (int i = pos + 1; i < length; ++i) {
      buf[i - 1] = buf[i];
    }

    // remove leading zeroes
    return buf[0] == '0' ? removeCharAt(buf, 0, newLength) : newLength;
  }
}
