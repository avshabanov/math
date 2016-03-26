import java.util.Arrays;

/**
 * Sample run:
 * <pre>
 * Given input= and template= result=
 * Given input=a and template=b result=
 * Given input=a and template=a result=a
 * Given input=abc and template=abc result=abc
 * Given input=cba and template=abc result=cba
 * Given input=agbaf and template=ab result=ba
 * Given input=ASDGSHEQRSFSDAGAXYYDFASYG and template=FGDA result=FSDAG
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class SmallestMatchingSubstringExample {

  public static void main(String[] args) {
    demo("", "");
    demo("a", "b");
    demo("a", "a");
    demo("abc", "abc");
    demo("cba", "abc");
    demo("agbaf", "ab");
    demo("ASDGSHEQRSFSDAGAXYYDFASYG", "FGDA");
  }

  public static void demo(String input, String source) {
    System.out.println("Given input=" + input + " and template=" + source +
            " result=" + getSmallestMatchingSubstring(input, source));
  }

  public static String getSmallestMatchingSubstring(String input, String source) {
    final char[] src = source.toCharArray();
    Arrays.sort(src);

    final char[] buf = new char[input.length()];

    for (int len = src.length; len <= input.length(); ++len) {
      final int maxPos = input.length() - len;
      for (int pos = 0; pos <= maxPos; ++pos) {
        input.getChars(pos, pos + len, buf, 0);
        Arrays.sort(buf, 0, len);

        if (match(src, buf, len)) {
          return input.substring(pos, pos + len);
        }
      }
    }

    return "";
  }

  private static boolean match(char[] template, char[] source, int len) {
    int it = 0;
    int is = 0;

    for (; it < template.length && is < len; ++is) {
      char ct = template[it];
      char cs = source[is];

      if (cs == ct) {
        ++it;
        continue;
      } else if (ct > cs) {
        continue;
      }
      return false;
    }


    return it == template.length;
  }
}
