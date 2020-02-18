package problems.leet100.longestPalindromicSubstring;

/**
 * https://leetcode.com/problems/longest-palindromic-substring/
 * 5. Longest Palindromic Substring
 */
public class LongestPalindromeSubstrSolution {

  public static void main(String[] args) {
    demo("ababababababa");
    demo("bananas");
    demo("abcdef");
    demo("abcdefg");
    demo("zaap");
    demo("zaaap");
    demo("zaaaap");

    demo("a");
    demo("zabap");

    demo("abba");
    demo("abcba");
    demo("abccba");
    demo("abcdcba");
    demo("abcddcba");
    demo("abcdedcba");

    demo("abbbbbba");
    demo("abbbbbbba");
    demo("abbbbbbbba");

    demo("zabbap");
    demo("zabcbap");
    demo("aqqzqqp");
    demo("babcddcbaf");
    demo("babcdfdcbaf");
    demo("qw0abcba0u");
  }

  private static void demo(String s) {
    System.out.printf("Longest palindrome in '%s' is '%s'\n", s,
        Solution.longestPalindrome(s));
  }

  private static final class Solution {
    static String longestPalindrome(String s) {
      if (s.isEmpty()) {
        return "";
      }

      int maxPalindromeOffset = 0;
      int maxPalindromeSize = 1;

      for (int i = 1; i < s.length(); ++i) {
        final int oddLength = computeMaxLength(s, i + 1, Math.min(i, s.length() - i - 1), 0);
        final int evenLength = computeMaxLength(s, i, Math.min(i, s.length() - i), -1);
        final int maxLength = Math.max(oddLength, evenLength);
        if (maxLength > maxPalindromeSize) {
          maxPalindromeSize = maxLength;
          maxPalindromeOffset = i - maxLength / 2;
        }
      }

      return s.substring(maxPalindromeOffset, maxPalindromeOffset + maxPalindromeSize);
    }

    static int computeMaxLength(String s, int startIndex, int size, int initialLength) {
      int length = initialLength;
      for (int j = 0; j < size; ++j) {
        final int nextLength = length + 2;
        if (s.charAt(startIndex + j) != s.charAt(startIndex + j - nextLength)) {
          break;
        }
        length = nextLength;
      }
      ++length;
      return length;
    }
  }
}
