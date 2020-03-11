package problems.leet100.minimumWindowSubstring;

import java.util.*;
import java.util.function.BiFunction;

/**
 * 76. Minimum Window Substring
 * https://leetcode.com/problems/minimum-window-substring/
 * <p>
 * Given a string S and a string T, find the minimum window in S which will contain all the characters in T in complexity O(n).
 * </p>
 * <p>
 * Example:
 * Input: S = "ADOBECODEBANC", T = "ABC"
 * Output: "BANC"
 *
 * Note:
 * If there is no such window in S that covers all characters in T, return the empty string "".
 * If there is such window, you are guaranteed that there will always be only one unique minimum window in S.
 * </p>
 *
 * minWindowLinear performance:
 * <p>
 * Runtime: 8 ms, faster than 73.24% of Java online submissions for Minimum Window Substring.
 * Memory Usage: 39.5 MB, less than 47.87% of Java online submissions for Minimum Window Substring.
 * </p>
 */
public class MinimumWindowSubstringSolution {

  public static void main(String[] args) {
    demo("A", "A", "A");
    demo("A", "B", "");
    demo("A", "AA", "");
    demo("AA", "AA", "AA");
    demo("AAAAAAABQQQCQQQABBC", "ABC", "ABBC");
    demo("AAA", "A", "A");
    demo("ADOBECODEBANC", "ABC", "BANC");
    demo("ABCDEFGHIJKLMNOPQRSTUVWXYZ", "QWE", "EFGHIJKLMNOPQRSTUVW");
    demo("ABCDEFG", "QWE", "");
    demo("ABQQAMNACZZBC", "ABC", "ACZZB");
    demo("ABQQAMNACZZBC", "AB", "AB");
  }

  private static final boolean USE_BRUTE_FORCE = Boolean.parseBoolean(System.getProperty("useBruteForce"));

  private static void demo(String s, String t, String expected) {
    BiFunction<String, String, String> minWindowFn;
    if (USE_BRUTE_FORCE) {
      minWindowFn = MinimumWindowSubstringSolution::minWindowBruteForce;
    } else {
      minWindowFn = MinimumWindowSubstringSolution::minWindowLinear;
    }


    final String actual = minWindowFn.apply(s, t);
    if (expected != null && !expected.equals(actual)) {
      throw new AssertionError("expected='" + expected + "' is not the same as '" + actual +
          "' for s='" + s + "' and t='" + t + "'");
    }
    System.out.printf("Input: s='%s', t='%s'\nOutput: '%s'\n", s, t, actual);
  }

  // Algorithm to find minimum window in O(n) amortized time, consuming O(n) space
  private static String minWindowLinear(String s, String t) {
    // shortcut for use cases when window is too small or too large
    if (s.isEmpty() || t.isEmpty() || t.length() > s.length()) {
      return "";
    }

    // shortcut for primitive case when pattern is a single character string
    if (t.length() == 1) {
      return s.contains(t) ? t : "";
    }

    // dissect template: collect total unique chars and prepare state for tracking each
    // matching characters
    int totalUniqueChars = 0;
    final Map<Character, CharStats> stats = new HashMap<>();
    for (int i = 0; i < t.length(); ++i) {
      final CharStats chst = stats.computeIfAbsent(t.charAt(i), (k) -> new CharStats());
      ++totalUniqueChars;
      ++chst.desiredCount;
    }

    int minStartIndex = 0;
    int minLastIndex = 0;

    // move window in the current string, expanding and shrinking it as needed
    for (int startIndex = 0, lastIndex = 0, charsFiltered = 0; lastIndex <= s.length();) {
      // 1st phase - expand window to have all the required chars
      while (lastIndex < s.length()) {
        final char ch = s.charAt(lastIndex);
        ++lastIndex;
        final CharStats chst = stats.get(ch);
        if (chst == null) {
          continue;
        }
        ++chst.iterationCount;
        if (chst.iterationCount > chst.desiredCount) {
          continue;
        }
        ++charsFiltered;
        if (charsFiltered == totalUniqueChars) {
          break;
        }
      }

      // quick test: if we weren't able to populate a window from startIndex offset,
      // there is no need to continue the search
      if (charsFiltered != totalUniqueChars) {
        break;
      }

      // perform initial update of the window
      if (minLastIndex == 0) {
        minStartIndex = startIndex;
        minLastIndex = lastIndex;
      }

      // 2nd phase - shrink window
      for (;;) {
        final char ch = s.charAt(startIndex);
        ++startIndex;
        final CharStats chst = stats.get(ch);

        if (chst != null) {
          chst.iterationCount--;
          if (chst.iterationCount < chst.desiredCount) {
            // this window is now broken and we should move forward
            --charsFiltered;
            break;
          }
        }

        // at this point we were able to shrink current window while retaining totalUniqueChars property
        if (lastIndex - startIndex < minLastIndex - minStartIndex) {
          minStartIndex = startIndex;
          minLastIndex = lastIndex;
        }
      }
    }

    return s.substring(minStartIndex, minLastIndex);
  }

  private static final class CharStats {
    int desiredCount;
    int iterationCount;

    @Override public String toString() { return "{target: " + desiredCount + ", cur: " + iterationCount + "}"; }
  }

  // Brute-force implementatino of minWindow
  private static String minWindowBruteForce(String s, String t) {
    final Map<Character, Integer> chars = new HashMap<>();
    for (int i = 0; i < t.length(); ++i) {
      chars.compute(t.charAt(i), (k, v) -> v == null ? 1 : v + 1);
    }

    int windowStart = 0;
    int windowEnd = -1;
    Map<Character, Integer> state = new HashMap<>(chars);
    for (int i = 0; i < s.length(); ++i) {
      final Character ch = s.charAt(i);

      if (state.containsKey(ch)) {
        int j = i;
        for (; !state.isEmpty() && (j < s.length()); ++j) {
          state.computeIfPresent(s.charAt(j), (k, v) -> v == 1 ? null : v - 1);
        }
        if (state.isEmpty()) {
           if (windowEnd < 0 || (j - i) < (windowEnd - windowStart)) {
            windowStart = i;
            windowEnd = j;
          }
        }
        state = new HashMap<>(chars);
      }
    }

    return windowEnd > 0 ? s.substring(windowStart, windowEnd) : "";
  }
}
