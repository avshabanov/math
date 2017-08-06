/**
 * See also <a href="https://leetcode.com/problems/regular-expression-matching/description/">Leetcode #10</a>.
 * 
 * <pre>
 * Implement regular expression matching with support for '.' and '*'.
 *  '.' Matches any single character.
 *  '*' Matches zero or more of the preceding element.
 *  The matching should cover the entire input string (not partial).
 * </pre>
 *
 * Result:
 * <pre>
 * A pattern=a* matches text=aaa
 * A pattern=a.* matches text=abc
 * A pattern=a* does not match text=abc
 * A pattern=a*bc matches text=abc
 * A pattern=abc* matches text=abc
 * A pattern=abc* matches text=abcc
 * A pattern=abc* does not match text=abccd
 * A pattern=abc* does not match text=abcd
 * A pattern=a.*f.h*i.*m matches text=abcdefghijklm
 * A pattern=a.*f.i*i.*m does not match text=abcdefghijklm
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
public final class SimpleRegexMatchingExample {

  public static void main(String[] args) {
    demo("aaa", "a*");
    demo("abc", "a.*");
    demo("abc", "a*");
    demo("abc", "a*bc");
    demo("abc", "abc*");
    demo("abcc", "abc*");
    demo("abccd", "abc*");
    demo("abcd", "abc*");
    demo("abcdefghijklm", "a.*f.h*i.*m");
    demo("abcdefghijklm", "a.*f.i*i.*m");
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

  private static boolean matches(String text, String pattern) {
    return matchesInternal(text, 0, pattern, 0);
  }

  private static boolean matchesInternal(String text, int textPos, String pattern, int patternPos) {
    // text pos came to an end? verify if pattern pos came to an end as well
    if (textPos == text.length()) {
      return pattern.length() == patternPos;
    }

    // pattern pos came to an end? => pattern does not match text
    if (pattern.length() == patternPos) {
      return false;
    }

    char patternChar = pattern.charAt(patternPos);
    final boolean charMatches;
    if (patternChar == '.') {
      charMatches = true;
    } else if (patternChar == '*') {
      throw new IllegalArgumentException("Unexpected pattern quantifier at " + patternPos + " in " + pattern);
    } else {
      charMatches = (text.charAt(textPos) == patternChar);
    }

    final int nextPatternPos = patternPos + 1;
    if (nextPatternPos < pattern.length()) {
      // special case: quantifier
      char nextPatternChar = pattern.charAt(nextPatternPos);
      if (nextPatternChar == '*') {
        // next char is a quantifier, try match arbitrary amount of characters and try to match
        if (charMatches && (matchesInternal(text, textPos + 1, pattern, patternPos) ||
            matchesInternal(text, textPos + 1, pattern, nextPatternPos + 1))) {
          return true;
        }

        // since this is a quantifier and previous matching efforts didn't yield true,
        // try to ignore this character w/quantifier
        return matchesInternal(text, textPos, pattern, nextPatternPos + 1);
      }
    }

    return charMatches && matchesInternal(text, textPos + 1, pattern, nextPatternPos);
  }
}
