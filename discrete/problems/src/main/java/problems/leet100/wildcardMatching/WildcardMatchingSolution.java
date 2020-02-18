package problems.leet100.wildcardMatching;

/**
 * 44. Wildcard Matching
 * https://leetcode.com/problems/wildcard-matching/
 *
 * <p>
 * Given an input string (s) and a pattern (p), implement wildcard pattern matching with support for '?' and '*'.
 *
 * '?' Matches any single character.
 * '*' Matches any sequence of characters (including the empty sequence).
 * The matching should cover the entire input string (not partial).
 *
 * Note:
 *
 * s could be empty and contains only lowercase letters a-z.
 * p could be empty and contains only lowercase letters a-z, and characters like ? or *.
 * </p>
 */
public class WildcardMatchingSolution {

  public static void main(String[] args) {
    demo("ab", "*a*");


    demo("", "");
    demo("a", "a");
    demo("aa", "aa");
    demo("aa", "*");

    demo("aa", "");
    demo("", "aa");
    demo("ab", "?b");
    demo("ab", "?a");
    demo("ab", "*");
    demo("ab", "*?*?*");

    demo("c", "*?*");
    demo("b", "?*?");
    demo("aaaa", "***a");

    demo("acdcb", "a*c?b");
    demo("adceb", "*a*b");

    demo("abcdefghijklmnop", "ab*gf*m*p");
    demo("abcdefghijklmnop", "ab*fg*m*p");
    demo("mississippi", "m??*ss*?i*pi");
    demo("bbbbbbbabbaabbabbbbaaabbabbabaaabbababbbabbbabaaabaab", "b*b*ab**ba*b**b***bba");

    // Verification in python:
    // import re
    // re.match('.*aa.*ba.*a.*bb.*aa.*ab.*a.*aaaaaa.*a.*aaaa.*bbabb.*b.*b.*aaaaaaaaa.*a.*ba.*bbb.*a.*ba.*bb.*bb.*a.*b.*bb', 'abbabaaabbabbaababbabbbbbabbbabbbabaaaaababababbbabababaabbababaabbbbbbaaaabababbbaabbbbaabbbbababababbaabbaababaabbbababababbbbaaabbbbbabaaaabbababbbbaababaabbababbbbbababbbabaaaaaaaabbbbbaabaaababaaaabb') == None
    demo(
        "abbabaaabbabbaababbabbbbbabbbabbbabaaaaababababbbabababaabbababaabbbbbbaaaabababbbaabbbbaabbbbababababbaabbaababaabbbababababbbbaaabbbbbabaaaabbababbbbaababaabbababbbbbababbbabaaaaaaaabbbbbaabaaababaaaabb",
        "**aa*****ba*a*bb**aa*ab****a*aaaaaa***a*aaaa**bbabb*b*b**aaaaaaaaa*a********ba*bbb***a*ba*bb*bb**a*b*bb"
    );
  }

  private static void demo(String s, String p) {
    System.out.printf("Matching '%s' with '%s':\n", s, p);

    long start;
    final long dpMatchTime;
    final long bruteForceTime;

    start = System.currentTimeMillis();
    boolean dpMatch = DynamicProgramming.isMatch(s, p);
    dpMatchTime = System.currentTimeMillis() - start;
    System.out.printf("\tDP matching [%d ms]: %b\n", dpMatchTime, dpMatch);

    if (p.length() < 25) {
      boolean bruteForceMatch;
      start = System.currentTimeMillis();
      bruteForceMatch = Bruteforce.isMatch(s, p);
      bruteForceTime = System.currentTimeMillis() - start;
      if (bruteForceMatch != dpMatch) {
        throw new AssertionError("Mismatch for source=" + s + " and pattern=" + p);
      }
      System.out.printf("\tBrute force [%d ms]: %b\n", bruteForceTime, bruteForceMatch);
    } else {
      System.out.println("\tBrute force skipped due to size of pattern\n");
    }

    System.out.println("---");
  }

  private static final class DynamicProgramming {
    static boolean isMatch(String s, String p) {
      // normalize pattern and source
      int lastStarIndex = -1;
      if (!p.isEmpty()) {
        final StringBuilder pattern = new StringBuilder(p.length());
        int offset = 0;

        for (int i = 0; i < p.length(); ++i) {
          final char ch = p.charAt(i);
          if (ch == '*') {
            lastStarIndex = i;
            if (i > 0 && p.charAt(i - 1) == '*') {
              continue;
            }
          }

          if (lastStarIndex < 0) {
            ++offset;
            if (i >= s.length()) {
              return false;
            }

            if (ch != '?' && s.charAt(i) != ch) {
              return false;
            }
          }

          pattern.append(ch);
        }

        p = pattern.substring(offset);
        s = s.substring(offset);
      }

      // shortcut: no wildcards
      if (lastStarIndex < 0) {
        return p.length() == s.length();
      }

      // shortcut: match empty string
      if (s.isEmpty()) {
        return p.equals("*");
      }

      final int[] dp = new int[s.length()];

      // offset in source array
      int srcOffset = 0;

      for (int i = 0; i < p.length(); ++i) {
        final char pch = p.charAt(i);
        if (pch == '*') {
          continue;
        }

        if (srcOffset >= s.length()) {
          return false;
        }

        int firstSrcPosition = -1;
        for (int j = s.length() - 1; j >= srcOffset; --j) {
          if ((i == 0 || p.charAt(i - 1) == '*' || dp[j - 1] == (i - 1)) &&
              (pch == '?' || s.charAt(j) == pch)) {
            firstSrcPosition = j; // set first position to adjust offset to
            dp[j] = i; // mark related cells as "reachable"
          }
        }
        if (firstSrcPosition < 0) {
          return false; // no such character met
        }
        srcOffset = firstSrcPosition + 1;
      }

      // at this point the entirety of the pattern has been matched,
      // we need to make sure every character has been accounted for
      if (p.charAt(p.length() - 1) == '*') {
        // disregard last source character: as long as the entire pattern matches, the rest doesn't matter
        return true;
      }
      return dp[s.length() - 1] == p.length() - 1; // make sure last character index matches last pattern character
    }
  }

  /** Straight recursion-based brute-force approach. Executes poorly timing-wise for big inputs. */
  private static final class Bruteforce {
    static boolean isMatch(String s, String p) {
      return isMatch(s, 0, p, 0);
    }

    private static boolean isMatch(String s, int spos, String p, int ppos) {
      if (spos >= s.length()) {
        // exhausted input string: accept this only if remainder pattern contents is all stars
        for (int i = ppos; i < p.length(); ++i) {
          if (p.charAt(i) != '*') {
            return false;
          }
        }
        return true;
      }

      if (ppos >= p.length()) {
        // exhausted pattern, yet there are chars in source string
        return false;
      }

      for (; spos < s.length() && ppos < p.length(); ++spos, ++ppos) {
        final char sch = s.charAt(spos);
        final char pch = p.charAt(ppos);
        if (pch == '?') {
          // unconditionally match these
          return isMatch(s, spos + 1, p, ppos + 1);
        }

        if (pch == '*') {
          for (; ppos < p.length(); ++ppos) {
            if (p.charAt(ppos) != '*') {
              break;
            }
          }

          // special case: match zero or more characters
          for (int i = spos; i <= s.length(); ++i) {
            if (isMatch(s, i, p, ppos)) {
              return true;
            }
          }
          return false;
        }

        if (sch != pch) {
          return false;
        }
      }


      return isMatch(s, spos, p, ppos);
    }
  }
}
