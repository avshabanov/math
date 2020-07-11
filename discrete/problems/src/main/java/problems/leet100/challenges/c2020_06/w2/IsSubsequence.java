package problems.leet100.challenges.c2020_06.w2;

import java.util.Arrays;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/540/week-2-june-8th-june-14th/3355/
 * <p>Given a string s and a string t, check if s is subsequence of t.
 *
 * A subsequence of a string is a new string which is formed from the original string by deleting some (can be none)
 * of the characters without disturbing the relative positions of the remaining characters. (ie, "ace" is a
 * subsequence of "abcde" while "aec" is not).
 *
 * Follow up:
 * If there are lots of incoming S, say S1, S2, ... , Sk where k >= 1B, and you want to check one by one to see if
 * T has its subsequence. In this scenario, how would you change your code?
 *
 * Credits:
 * Special thanks to @pbrother for adding this problem and creating all test cases.
 *
 *
 *
 * Example 1:
 *
 * Input: s = "abc", t = "ahbgdc"
 * Output: true
 * Example 2:
 *
 * Input: s = "axc", t = "ahbgdc"
 * Output: false
 *
 *
 * Constraints:
 *
 * 0 <= s.length <= 100
 * 0 <= t.length <= 10^4
 * Both strings consists only of lowercase characters.</p>
 */
public class IsSubsequence {
  public static void main(String[] args) {
    System.out.println("t0 = " + isSubsequence("ace", "abcde"));
    System.out.println("t1 = " + isSubsequence("aaaaaa", "bbaaaa"));
    System.out.println("t2 = " + isSubsequence("aec", "abcde"));
    System.out.println("t3 = " + isSubsequence("a", "a"));
    System.out.println("t4 = " + isSubsequence("a", "b"));
  }

  private static boolean isSubsequence(String s, String t) {
    for (int i = 0, j = 0; i < s.length(); ++i) {
      final char ch = s.charAt(i);
      boolean found = false;
      for (; j < t.length() && !found; ++j) {
        if (t.charAt(j) == ch) {
          found = true;
        }
      }
      if (!found) {
        return false;
      }
    }
    return true;
  }

  //
  // Follow-up: Transform input string into a prefix-alike tree, so that each
  // char is referring to first occurrences of all unique chars that follow after.
  // Finding a match is then a matter of traversing this tree for input string starting from the root
  //

  public static final class OccurrenceTree {
    private static final int UNIQUE_CHARS_COUNT = 'z' - 'a' + 1;
    private final String input;
    /**
     * Each char at UNIQUE_CHARS_COUNT * pos is referring to UNIQUE_CHARS_COUNT char indices
     */
    private final short[] indices;

    OccurrenceTree(String input) {
      this.input = input;
      final int indicesLength = input.length() * UNIQUE_CHARS_COUNT;
      if (indicesLength > Short.MAX_VALUE) {
        throw new IllegalStateException("Input string is too big");
      }
      this.indices = new short[input.length() * UNIQUE_CHARS_COUNT];
      initializeIndices();
    }

    private void initializeIndices() {
      Arrays.fill(indices, (short) -1);
      // TODO: implement
    }

    boolean isSubsequence(String s) {
      if (s.length() > input.length()) {
        return false;
      }

      int pos = 0;
      for (int i = 0; i < s.length() && pos < input.length(); ++i) {
        int charIndex = s.charAt(i) - 'a';
        if (charIndex < 0 || charIndex >= UNIQUE_CHARS_COUNT) {
          // unknown character
          return false;
        }

        final int nextIndex = indices[pos + charIndex];
        if (nextIndex < 0) {
          return false;
        }
        pos = nextIndex;
      }
      return true;
    }
  }
}
