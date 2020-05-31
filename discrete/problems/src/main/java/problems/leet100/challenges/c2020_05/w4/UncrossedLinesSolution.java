package problems.leet100.challenges.c2020_05.w4;

import java.util.Arrays;
import java.util.function.BiFunction;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/537/week-4-may-22nd-may-28th/3340/
 * <p>We write the integers of A and B (in the order they are given) on two separate horizontal lines.
 *
 * Now, we may draw connecting lines: a straight line connecting two numbers A[i] and B[j] such that:
 *
 * A[i] == B[j];
 * The line we draw does not intersect any other connecting (non-horizontal) line.
 * Note that a connecting lines cannot intersect even at the endpoints: each number can only belong to one connecting line.
 *
 * Return the maximum number of connecting lines we can draw in this way.</p>
 * <p>Note:
 *
 * 1 <= A.length <= 500
 * 1 <= B.length <= 500
 * 1 <= A[i], B[i] <= 2000</p>
 */
public class UncrossedLinesSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(3, new int[]{2,5,1,2,5}, new int[]{10,5,2,1,5,2});
      demo(2, new int[]{1,3,7,1,7,5}, new int[]{1,9,2,5,1});
      demo(1, new int[]{1}, new int[]{1,3});
      demo(4, new int[]{2,1,2,1,2}, new int[]{1,2,1,2,1});
      demo(3, new int[]{1,1,2,1,2}, new int[]{1,3,2,3,1});
      System.out.println("OK");
    }
  }

  private static void demo(int expected, int[] a, int[] b) {
    BiFunction<int[], int[], Integer> finder = RecursiveSolution::maxUncrossedLines;
    if (Boolean.parseBoolean(System.getProperty("useRecursive"))) {
      finder = DPSolution::maxUncrossedLines;
    }

    final int result = finder.apply(a, b);
    final String aStr = Arrays.toString(a);
    final String bStr = Arrays.toString(b);

    if (result != expected) {
      throw new AssertionError("Expected: " + expected + ", actual: " + result + " for a=" + aStr + " and b=" + bStr);
    }

    System.out.printf("Input: a=%s, b=%s\nOutput: %d\n", aStr, bStr, result);
  }

  private static final class DPSolution {
    static int maxUncrossedLines(int[] a, int[] b) {
      if (a.length == 0 || b.length == 0) {
        return 0;
      }

      int[][] dp = new int[a.length][];
      for (int i = 0; i < a.length; ++i) {
        dp[i] = new int[b.length];
        for (int j = 0; j < b.length; ++j) {

          if (a[i] == b[j]) {
            dp[i][j] = 1 + ((i > 0 && j > 0) ? dp[i - 1][j - 1] : 0);
          } else {
            dp[i][j] = Math.max(i > 0 ? dp[i - 1][j] : 0, j > 0 ? dp[i][j - 1] : 0);
          }
        }
      }

      return dp[a.length - 1][b.length - 1];
    }
  }

  private static final class InlineRecursiveSolution {
    static int maxUncrossedLines(int[] a, int[] b) {
      if (a.length == 0 || b.length == 0) {
        return 0;
      }

      final Pair[] pairs = new Pair[Math.min(a.length, b.length)];
      for (int i = 0; i < pairs.length; ++i) {
        pairs[i] = new Pair();
      }
      int depth = 0;
      int max = 0;
      int aStart = 0;
      int bStart = 0;

      LOuter:
      for (;;) {

        for (int i = aStart; i < a.length; ++i) {
          for (int j = bStart; j < b.length; ++j) {
            if (a[i] == b[j]) {
              final Pair p = pairs[depth];
              p.i = i + 1;
              p.j = j + 1;
              ++depth;
              aStart = i + 1;
              bStart = j + 1;
              continue LOuter;
            }
          }
        }

        max = Math.max(max, depth);

        if (depth > 0) {
          --depth;
          final Pair p = pairs[depth];
          aStart = p.i;
          bStart = p.j;
        } else {
          break;
        }
      }

      return max;
    }

    static final class Pair {
      int i;
      int j;
    }
  }

  // exceeds time limit
  private static final class RecursiveSolution {
    static int maxUncrossedLines(int[] a, int[] b) {
      if (a.length == 0 || b.length == 0) {
        return 0;
      }
      final RecursiveFinder finder = new RecursiveFinder(a, b);
      finder.scan(0, 0, 0);
      return finder.max;
    }

    private static final class RecursiveFinder {
      final int[] a;
      final int[] b;
      int max;

      RecursiveFinder(int[] a, int[] b) {
        this.a = a;
        this.b = b;
      }

      void scan(int ia, int ib, int depth) {
        for (int i = ia; i < a.length; ++i) {
          for (int j = ib; j < b.length; ++j) {
            if (a[i] == b[j]) {
              scan(i + 1, j + 1, depth + 1);
            }
          }
        }

        max = Math.max(max, depth);
      }
    }
  }
}
