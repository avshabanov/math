package problems.leet100.challenges.cmisc;

import java.util.function.Function;

/**
 * Climbing Stairs
 * You are climbing a stair case. It takes n steps to reach to the top.
 * Each time you can either climb 1 or 2 steps. In how many distinct ways can you climb to the top?
 *
 * Constraints:
 *
 * 1 <= n <= 45
 */
public class ClimbingStairs {

  public static final class Demo1 {
    public static void main(String[] args) {
      final String arg = args.length > 0 ? args[0] : "";
      Function<Integer, Integer> climbStairs = BruteForce::climbStairs;
      if (!arg.equals("1")) {
        climbStairs = FibMathSolution::climbStairs;
      }
      for (int i = 1; i < 12; i++) {
        System.out.println("For i=" + i + " climbStairs=" + climbStairs.apply(i));
      }
    }
  }

  private static final class FibMathSolution {
    private static final double SQRT5 = Math.sqrt(5.0);

    // taken from https://leetcode.com/articles/climbing-stairs/
    private static int climbStairs(int n) {
      double fibn = Math.pow((1 + SQRT5) / 2, n + 1) - Math.pow((1 - SQRT5) / 2, n + 1);
      return (int)(fibn / SQRT5);
    }
  }

  private static final class FibSolution {
    private static int climbStairs(int n) {
      if (n == 1) {
        return 1;
      }

      int a = 1;
      int result = 2;
      for (int i = 3; i <= n; ++i) {
        final int tmp = result;
        result = a + result;
        a = tmp;
      }
      return result;
    }
  }

  private static final class MemoizeSolution {


    private static int climbStairs(int n) {
      final MemoizeFinder memoizeFinder = new MemoizeFinder();
      return memoizeFinder.compute(n);
    }

    private static final class MemoizeFinder {
      private static final int MAX_VAL = 45;

      private final int[] dp = new int[MAX_VAL + 1];

      public MemoizeFinder() {
        dp[1] = 1;
        dp[2] = 2;
      }

      int compute(int n) {
        if (dp[n] != 0) {
          return dp[n];
        }
        final int result = compute(n - 1) + compute(n - 2);
        dp[n] = result;
        return result;
      }
    }
  }

  private static final class BruteForce {

    private final int sum;
    private int acc;

    public BruteForce(int sum) {
      this.sum = sum;
    }

    public void find(int cur) {
      if (cur == sum) {
        ++acc;
        return;
      } else if (cur > sum) {
        return;
      }
      find(cur + 1);
      find(cur + 2);
    }

    private static int climbStairs(int n) {
      final BruteForce bruteForce = new BruteForce(n);
      bruteForce.find(0);
      return bruteForce.acc;
    }
  }
}
