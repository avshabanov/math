/**
 * Problem:
 * <p>Given a string, find largest substring which is lexicographically greater than original one.</p>
 *
 * Sample run:
 * <pre>
 * Given string= largest substring=null
 * Given string=a largest substring=null
 * Given string=ab largest substring=b
 * Given string=ba largest substring=null
 * Given string=bac largest substring=c
 * Given string=bcaf largest substring=caf
 * Given string=bbbacaaa largest substring=caaa
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class BiggerSubstringExample {

  public static void main(String[] args) {
    demo("");
    demo("a");
    demo("ab");
    demo("ba");
    demo("bac");
    demo("bcaf");
    demo("bbbacaaa");
  }

  public static void demo(String str) {
    System.out.println("Given string=" + str + " largest substring=" + getLargestSubstring(str));
  }

  public static String getLargestSubstring(String src) {
    for (int i = src.length() - 1; i >= 1; --i) {
      for (int j = 1; j <= src.length() - i; ++j) {
        if (isSubstringGreaterThanOriginalString(src, j, i)) {
          return src.substring(j, j + i);
        }
      }
    }

    return null;
  }

  public static boolean isSubstringGreaterThanOriginalString(String src, int startIndex, int length) {
    for (int i = 0; i < length; ++i) {
      final int cmp = ((int) src.charAt(i)) - src.charAt(startIndex + i);
      if (cmp < 0) {
        return true;
      } else if (cmp > 0) {
        return false;
      }
    }
    return false;
  }
}
