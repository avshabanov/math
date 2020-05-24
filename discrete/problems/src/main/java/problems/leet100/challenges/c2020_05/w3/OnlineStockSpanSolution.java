package problems.leet100.challenges.c2020_05.w3;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Deque;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/536/week-3-may-15th-may-21st/3334/
 * <p>Write a class StockSpanner which collects daily price quotes for some stock, and returns the span of
 * that stock's price for the current day.
 *
 * The span of the stock's price today is defined as the maximum number of consecutive days (starting from today and
 * going backwards) for which the price of the stock was less than or equal to today's price.
 *
 * For example, if the price of a stock over the next 7 days were [100, 80, 60, 70, 60, 75, 85], then the stock spans
 * would be [1, 1, 1, 2, 1, 4, 6].</p>
 * <p>Note:
 * Calls to StockSpanner.next(int price) will have 1 <= price <= 10^5.
 * There will be at most 10000 calls to StockSpanner.next per test case.
 * There will be at most 150000 calls to StockSpanner.next across all test cases.
 * The total time limit for this problem has been reduced by 75% for C++, and 50% for all other languages.</p>
 */
public class OnlineStockSpanSolution {

  public static void main(String[] args) {
    demo(10);
    demo(100, 80, 60, 70, 60, 75, 85);
  }

  private static void demo(int... prices) {
    final StockSpanner spanner = new StockSpanner();
    final int[] days = Arrays.stream(prices).map(spanner::next).toArray();
    System.out.printf("Input: %s\nOutput: %s\n", Arrays.toString(prices), Arrays.toString(days));
  }

  private static final class StockSpanner {
    final Deque<Ent> deque = new ArrayDeque<>();

    private static final class Ent {
      final int price;
      int days;

      public Ent(int price) {
        this.price = price;
        this.days = 1;
      }
    }

    public int next(int price) {
      final Ent e = new Ent(price);
      while (!deque.isEmpty()) {
        final Ent other = deque.peekLast();
        if (other.price > price) {
          break;
        }
        e.days += other.days;
        deque.pollLast();
      }
      deque.addLast(e);
      return e.days;
    }
  }
}
