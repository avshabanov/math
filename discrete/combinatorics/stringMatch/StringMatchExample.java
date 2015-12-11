/**
 * Demonstrates simple string pattern matching.
 * <p>
 * A pattern can have two types of special characters:
 * </p>
 * <ul>
 *   <li><code>?</code> - matches any character</li>
 *   <li><code>*</code> - matches any group of characters</li>
 * </ul>
 *
 * <p>Sample output:</p>
 * <pre>
 * [OK] A pattern '' matches ''.
 * [OK] A pattern '*' matches ''.
 * [OK] A pattern '?' does not match ''.
 * [OK] A pattern '*' matches 'a'.
 * [OK] A pattern '?' matches 'a'.
 * [OK] A pattern 'a' does not match ''.
 * [OK] A pattern '' does not match 'a'.
 * [OK] A pattern 'abc' matches 'abc'.
 * [OK] A pattern 'a*e?g' matches 'abcdefg'.
 * [OK] A pattern 'a*d?g' does not match 'abcdefg'.
 * [OK] A pattern '*z' matches 'xyz'.
 * [OK] A pattern '*f' does not match 'xyz'.
 * [OK] A pattern 'z*' does not match 'xyz'.
 * [OK] A pattern 'a?c*fg*m?op' matches 'abcdefghijklmnop'.
 * [OK] A pattern 'a?c*gf*m?op' does not match 'abcdefghijklmnop'.
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class StringMatchExample {

  public static void main(String[] args) {
    demo("", "", true);
    demo("", "*", true);
    demo("", "?", false);
    demo("a", "*", true);
    demo("a", "?", true);
    demo("", "a", false);
    demo("a", "", false);
    demo("abc", "abc", true);
    demo("abcdefg", "a*e?g", true);
    demo("abcdefg", "a*d?g", false);
    demo("xyz", "*z", true);
    demo("xyz", "*f", false);
    demo("xyz", "z*", false);
    demo("abcdefghijklmnop", "a?c*fg*m?op", true);
    demo("abcdefghijklmnop", "a?c*gf*m?op", false);
  }

  static void demo(String source, String pattern, boolean shouldMatch) {
    final boolean matchResult = matches(source, pattern);
    if (matchResult == shouldMatch) {
      System.out.println("[OK] A pattern '" + pattern + "' " +
          (shouldMatch ? "matches" : "does not match") + " '" + source + "'.");
      return;
    }

    throw new AssertionError("Incorrect match result for pattern='" + pattern + "' and source='" + source +
        "' - " + (matchResult ? "matches" : "does not match") + ".");
  }

  //
  // Private
  //

  private static boolean matches(String source, String pattern) {
    return matchesInternal(source, 0, pattern, 0);
  }

  private static boolean matchesInternal(String s, int spos, String p, int ppos) {
    // end of string?
    if (p.length() == ppos) {
      return s.length() == spos;
    }

    // match character
    final char pch = p.charAt(ppos);
    if (pch == '*') {
      if (s.isEmpty()) {
        // source string is empty - try next character
        return matchesInternal(s, spos, p, ppos + 1);
      }

      // try to use any number of characters
      for (int i = spos; i <= s.length(); ++i) {
        // try any number of characters
        final boolean result = matchesInternal(s, i, p, ppos + 1);
        if (result) {
          return true;
        }
      }
      return false;
    }

    if (s.length() <= spos) {
      return false; // source string is too small
    }

    if (pch == '?') {
      // question mark matches any character
      return matchesInternal(s, spos + 1, p, ppos + 1);
    }

    // match character (equality check)
    final char sch = s.charAt(spos);
    return sch == pch && matchesInternal(s, spos + 1, p, ppos + 1);
  }
}
