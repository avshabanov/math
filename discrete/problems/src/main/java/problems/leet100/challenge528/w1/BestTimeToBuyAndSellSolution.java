package problems.leet100.challenge528.w1;

import java.util.Arrays;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/528/week-1/3287/
 * <p>
 * Say you have an array for which the ith element is the price of a given stock on day i.
 * Design an algorithm to find the maximum profit. You may complete as many transactions as you like (i.e.,
 * buy one and sell one share of the stock multiple times).
 * Note: You may not engage in multiple transactions at the same time (i.e., you must sell the stock before you buy
 * again).
 * </p>
 */
public class BestTimeToBuyAndSellSolution {

  public static void main(String[] args) {
    demo(7,1,5,3,6,4);
    demo(1,2,3,4,5);
    demo(7,6,4,3,1);
  }

  private static void demo(int... prices) {
    System.out.printf("Input: %s\nOutput: %s\n", Arrays.toString(prices), maxProfit(prices));
  }

  private static int maxProfit(int[] prices) {
    if (prices.length == 0) {
      return 0;
    }

    int profit = 0;
    int prevPrice = prices[0];
    int startSlopePrice = prevPrice;

    for (int i = 1; i <= prices.length; ++i) {
      final int price = i == prices.length ? Integer.MIN_VALUE : prices[i];
      if (price < prevPrice) {
        profit += (prevPrice - startSlopePrice);
        startSlopePrice = price;
      }
      prevPrice = price;
    }

    return profit;
  }
}
