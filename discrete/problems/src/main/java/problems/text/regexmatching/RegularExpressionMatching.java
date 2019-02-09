package problems.text.regexmatching;

/**
 * Solution for "Regular Expression Matching" problem - https://leetcode.com/problems/regular-expression-matching/
 */
public final class RegularExpressionMatching {

  private static boolean isMatch(String s, String p) {
    return isMatch(s, 0, p, 0);
  }

  private static boolean isMatch(String src, int srcPos, String pattern, int patternPos) {
    int nextPatternPos;
    for (; patternPos < pattern.length(); patternPos = nextPatternPos) {
      final char patternChar = pattern.charAt(patternPos);
      nextPatternPos = patternPos + 1;

      // lookahead for star-symbol
      if (nextPatternPos < pattern.length() && pattern.charAt(nextPatternPos) == '*') {
        ++nextPatternPos;
        if (isMatch(src, srcPos, pattern, nextPatternPos)) {
          return true;
        }

        // match character one or more times
        for (int i = srcPos; i < src.length(); ++i) {
          final char srcChar = src.charAt(i);
          if (!isExactMatch(srcChar, patternChar)) {
            return false;
          }

          if (isMatch(src, i + 1, pattern, nextPatternPos)) {
            return true;
          }
        }

        return false; // can't match this sequence at all
      }

      if (srcPos < src.length()) {
        final char srcChar = src.charAt(srcPos);
        if (isExactMatch(srcChar, patternChar)) {
          // move to the next symbol
          ++srcPos;
          continue;
        }
      }

      return false;
    }

    // pattern exhausted and all its symbols matched, now check if source is exhausted too
    return src.length() == srcPos;
  }

  private static boolean isExactMatch(char srcChar, char patternChar) {
    return (patternChar == '.') || (srcChar == patternChar);
  }

  //
  // Demo
  //

  private static void demo(String s, String p) {
    System.out.println(String.format("match('%s', '%s') = %s", s, p, isMatch(s, p)));
  }

  public static final class Demo1 {
    public static void main(String[] args) {
      demo("", "");
      demo("", ".*");
      demo("a", "a");
      demo("a", "aa");
      demo("aa", "a");
      demo("aa", "a.");
      demo("a", "a*");
      demo("bc", "a*b*c");
    }
  }
}
