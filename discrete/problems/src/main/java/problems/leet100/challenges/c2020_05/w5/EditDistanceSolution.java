package problems.leet100.challenges.c2020_05.w5;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/538/week-5-may-29th-may-31st/3346/
 * <p>Given two words word1 and word2, find the minimum number of operations required to convert word1 to word2.
 *
 * You have the following 3 operations permitted on a word:
 *
 * Insert a character
 * Delete a character
 * Replace a character</p>
 */
public class EditDistanceSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo("a", "b");
      demo("a", "a");
      demo("horse", "rose");
      demo("horse", "ros");
      demo("intention", "execution");
    }
  }

  private static void demo(String word1, String word2) {
    System.out.printf(
        "Input: %s, %s\nOutput: %d\n---\n",
        word1,
        word2,
        minDistance(word1, word2)
    );
  }

  /*

       h  o  r  s  e
    r  1  2  2  3  4
    o
    s
    e
   */

  private static int minDistance(String word1, String word2) {
    if (word1.length() == 0 || word2.length() == 0) {
      return Math.max(word1.length(), word2.length());
    }

    final int[][] dp = new int[word1.length() + 1][];

    for (int i = 0; i <= word1.length(); ++i) {
      dp[i] = new int[word2.length() + 1];
      dp[i][0] = i;
    }

    for (int j = 0; j <= word2.length(); ++j) {
      dp[0][j] = j;
    }

    for (int i = 1; i <= word1.length(); ++i) {
      for (int j = 1; j <= word2.length(); ++j) {
        dp[i][j] = Math.min(
            1 + dp[i - 1][j],
            Math.min(
                1 + dp[i][j - 1],
                dp[i - 1][j - 1] + (word1.charAt(i - 1) == word2.charAt(j - 1) ? 0 : 1)
            )
        );
      }
    }

    return dp[word1.length()][word2.length()];
  }
}
