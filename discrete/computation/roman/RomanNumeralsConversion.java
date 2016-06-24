import java.util.ArrayList;
import java.util.List;

/**
 * Sample run:
 * <pre>
 * Number 1 as roman is I
 * Number 19 as roman is XIX
 * Number 888 as roman is DCCCLXXXVIII
 * Number 1954 as roman is MCMLIV
 * Number 3124 as roman is MMMCXXIV
 * </pre>
 *
 * @author Alexander Shabanov
 */
public class RomanNumeralsConversion {

  public static void main(String[] args) {
    demo(1);
    demo(19);
    demo(888);
    demo(1954);
    demo(3124);
  }

  public static void demo(int num) {
    System.out.println("Number " + num + " as roman is " + toRomanNumber(num));
  }

  private static final String[][] ROMAN_NUMERALS = {
    { "I", "II", "III", "IV", "V", "VI", "VII", "VIII", "IX" },
    { "X", "XX", "XXX", "XL", "L", "LX", "LXX", "LXXX", "XC" },
    { "C", "CC", "CCC", "CD", "D", "DC", "DCC", "DCCC", "CM" },
    { "M", "MM", "MMM" }
  };

  private static String toRomanNumber(int num) {
    final List<String> result = new ArrayList<>();
    if (num < 0) {
      result.add("-"); // Romans didn't know about negative numbers, but let it still be
    }

    for (int pos = 0; num != 0; num = num / 10, pos = pos + 1) {
      if (pos < ROMAN_NUMERALS.length) {
        final String[] numerals = ROMAN_NUMERALS[pos];
        int digit = num % 10;
        if (digit == 0) {
          continue;
        }

        digit = digit - 1;

        if (digit < numerals.length) {
          result.add(0, numerals[digit]);
          continue;
        }
      }
      throw new IllegalArgumentException("Number is too big");
    }

    return String.join("", result);
  }
}
