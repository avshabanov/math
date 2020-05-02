package problems.leet100.challenges.c2020_04.w1;

import java.util.HashSet;
import java.util.Set;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/528/week-1/3284/
 *
 * <p>
 * Write an algorithm to determine if a number n is "happy".
 *
 * A happy number is a number defined by the following process: Starting with any positive integer, replace the number
 * by the sum of the squares of its digits, and repeat the process until the number equals 1 (where it will stay), or
 * it loops endlessly in a cycle which does not include 1.
 * Those numbers for which this process ends in 1 are happy numbers.
 *
 * Return True if n is a happy number, and False if not.
 * </p>
 */
public class HappyNumberSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(19);
      demo(5);
    }
  }

  private static void demo(int n) {
    System.out.printf("Input: %d\nOutput: %s\n", n, isHappy(n));
  }

  private static boolean isHappy(int n) {
    final Set<Integer> intSet = new HashSet<>();
    for (;;) {
      n = sumOfDigitSquares(n);
      if (n == 1) {
        return true;
      }
      if (!intSet.add(n)) {
        return false;
      }
    }
  }

  private static int sumOfDigitSquares(int k) {
    int result = 0;
    while (k != 0) {
      final int digit = k % 10;
      result += (digit * digit);
      k /= 10;
    }
    return result;
  }
}
