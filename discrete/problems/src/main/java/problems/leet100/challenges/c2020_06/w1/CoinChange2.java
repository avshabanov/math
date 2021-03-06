package problems.leet100.challenges.c2020_06.w1;

import java.util.Arrays;
import java.util.TreeSet;
import java.util.stream.Collectors;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/539/week-1-june-1st-june-7th/3353/
 * <p>You are given coins of different denominations and a total amount of money.
 * Write a function to compute the number of combinations that make up that amount. You may assume that you have
 * infinite number of each kind of coin.
 *
 * Example 1:
 *
 * Input: amount = 5, coins = [1, 2, 5]
 * Output: 4
 * Explanation: there are four ways to make up the amount:
 * 5=5
 * 5=2+2+1
 * 5=2+1+1+1
 * 5=1+1+1+1+1
 * Example 2:
 *
 * Input: amount = 3, coins = [2]
 * Output: 0
 * Explanation: the amount of 3 cannot be made up just with coins of 2.
 * Example 3:
 *
 * Input: amount = 10, coins = [10]
 * Output: 1
 *
 *
 * Note:
 *
 * You can assume that
 *
 * 0 <= amount <= 5000
 * 1 <= coin <= 5000
 * the number of coins is less than 500
 * the answer is guaranteed to fit into signed 32-bit integer</p>
 */
public class CoinChange2 {

  public static void main(String[] args) {
    System.out.println("c4 = " + change(10, new int[] {5, 1, 2}));

    System.out.println("c0 = " + change(0, new int[] {}));
    System.out.println("c1 = " + change(3, new int[] {1, 2}));
    System.out.println("c2 = " + change(5, new int[] {5, 1, 2}));
    System.out.println("c3 = " + change(3, new int[] {2}));

  }

  private static int change(int amount, int[] coins) {
    coins = new TreeSet<>(Arrays.stream(coins).boxed().collect(Collectors.toList())).stream()
        .mapToInt(Integer::intValue).toArray();

    final int[] dp = new int[amount + 1];
    dp[0] = 1;
    for (int coin : coins) {
      for (int i = 0; ; ++i) {
        final int target = i + coin;
        if (target > amount) {
          break;
        }
        dp[target] = dp[i] + dp[target];
      }
    }
    return dp[amount];
  }
}
