package problems.leet100.challenges.c2020_04.w4;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/531/week-4/3311/
 * <p>Given two strings text1 and text2, return the length of their longest common subsequence.
 *
 * A subsequence of a string is a new string generated from the original string with some characters(can be none)
 * deleted without changing the relative order of the remaining characters. (eg, "ace" is a subsequence of "abcde"
 * while "aec" is not). A common subsequence of two strings is a subsequence that is common to both strings.
 *
 * If there is no common subsequence, return 0.</p>
 */
public class LongestCommonSubsequenceSolution {

  public static final class Demo1 {

    public static void main(String[] args) {
      final int d3 = longestCommonSubsequence("abcde", "ace");
      System.out.printf("d3 = %d\n", d3);

      final int d1 = longestCommonSubsequence("abcdef", "dbghd");
      System.out.printf("d1 = %d\n", d1);

      final int d2 = longestCommonSubsequence("abc", "cba");
      System.out.printf("d2 = %d\n", d2);
    }
  }

  private static int longestCommonSubsequence(String text1, String text2) {
    // use dynamic programming, so that position at (i,j) is
    // the longest common subsequence of text1[0..i] and text2[0..j]
    final int[][] dp = new int[text1.length()][];
    for (int i = 0; i < text1.length(); ++i) {
      final char c1 = text1.charAt(i);
      dp[i] = new int[text2.length()];
      for (int j = 0; j < text2.length(); ++j) {
        // induction: use previously calculated subsequence if characters at current positions match, otherwise
        // use max subsequences taking fewer characters from either first or second string
        final char c2 = text2.charAt(j);
        if (c1 == c2) {
          dp[i][j] = 1 + ((i > 0 && j > 0) ? dp[i - 1][j - 1] : 0);
          continue;
        }

        final int left = (i > 0 ? dp[i - 1][j] : 0);
        final int right = (j > 0 ? dp[i][j - 1] : 0);
        dp[i][j] = Math.max(left, right);
      }
    }
    return dp[text1.length() - 1][text2.length() - 1];
  }
}
