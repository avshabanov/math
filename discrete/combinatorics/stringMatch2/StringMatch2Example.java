/**
 * Pattern matching with special quantifier character - '*' that means match previous character zero or more times.
 * Dot character means any character.
 *
 * Sample run:
 * <pre>
 * A pattern=a* matches text=aaa
 * A pattern=a.* matches text=abc
 * A pattern= matches text=
 * A pattern=a matches text=a
 * A pattern=b does not match text=a
 * A pattern=abc matches text=abc
 * A pattern=a.c matches text=abc
 * A pattern=a.c does not match text=abcd
 * A pattern=a.c does not match text=abd
 * A pattern=a.. matches text=abd
 * A pattern=a.* matches text=abd
 * A pattern=a.*b matches text=ab
 * A pattern=a*b matches text=ab
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class StringMatch2Example {

  public static void main(String[] args) {
    demo("aaa", "a*");
    demo("abc", "a.*");
    demo("abc", "a*");
    demo("abc", "a*bc");
    //demo("abc", "abc*"); - bug
    demo("", "");
    demo("a", "a");
    demo("a", "b");
    demo("abc", "abc");
    demo("abc", "a.c");
    demo("abcd", "a.c");
    demo("abd", "a.c");
    demo("abd", "a..");
    demo("abd", "a.*");
    demo("ab", "a.*b");
    demo("ab", "a*b");
  }

  public static void demo(String text, String pattern) {
    System.out.println("A pattern=" + pattern + " " + (matches(text, pattern) ? "matches" : "does not match") +
        " text=" + text);
  }

  public static boolean matches(String text, String pattern) {
    final MatchHelper helper = new MatchHelper(text, pattern);
    return helper.matches(0, 0);
  }

  private static final class MatchHelper {
    private final String text;
    private final String pattern;

    public MatchHelper(String text, String pattern) {
      this.text = text;
      this.pattern = pattern;
    }

    boolean matches(int textPos, int patternPos) {
      int tp = textPos;

      for (int pp = patternPos; pp < pattern.length(); ++pp) {
        final char pch = pattern.charAt(pp);
        if (pch == '*') {
          throw new IllegalArgumentException("Quantifier character without preceding character is not allowed");
        }

        boolean charMatches = true;
        if (tp >= text.length()) {
          charMatches = false;
        } else {
          final char tch = text.charAt(tp);
          if (pch != '.' && pch != tch) {
            charMatches = false; // mismatch at corresponding position
          }
        }

        // lookahead for quantifier
        final int patternLookaheadPos = pp + 1;
        if (patternLookaheadPos < pattern.length() && pattern.charAt(patternLookaheadPos) == '*') {
          if (matches(textPos, patternLookaheadPos + 1)) {
            return true;
          }

          return charMatches && matches(textPos + 1, pp);
        }

        if (!charMatches) {
          return false;
        }

        ++tp;
      }

      return tp == text.length();
    }
  }
}
