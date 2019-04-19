package problems.combinatorics;

import lombok.AllArgsConstructor;

/**
 * Finds integer solutions for diophantine equation:
 * x**3 + y**3 + z**3 = n
 */
public class Cube3Sum {

  private enum Sign {
    PLUS("+"),
    MINUS("-");

    private final String op;

    Sign(String op) {
      this.op = op;
    }
  }

  @AllArgsConstructor
  private static final class Solution {
    Sign sign1;
    int a;
    Sign sign2;
    int b;
    Sign sign3;
    int c;

    @Override
    public String toString() {
      return sign1.op + a + "**3 " + sign2.op + " " + b + "**3 " + sign3.op + " " + c + "**3";
    }
  }

  private static final int BOUND = 1000;

  private static Solution bruteForceFind(int n) {
    for (int a = 1; a < BOUND; ++a) {
      final long a3 = ((long) a) * a * a;
      for (int b = a; b < BOUND; ++b) {
        final long b3 = ((long) b) * b * b;
        for (int c = b; c < BOUND; ++c) {
          final long c3 = ((long) c) * c * c;
          long sum;

          // + + +
          sum = a3 + b3 + c3;
          if (sum == n) {
            return new Solution(Sign.PLUS, a, Sign.PLUS, b, Sign.PLUS, c);
          }

          // + + -
          sum = a3 + b3 - c3;
          if (sum == n) {
            return new Solution(Sign.PLUS, a, Sign.PLUS, b, Sign.MINUS, c);
          }

          // + - +
          sum = a3 - b3 + c3;
          if (sum == n) {
            return new Solution(Sign.PLUS, a, Sign.MINUS, b, Sign.PLUS, c);
          }

          // + - -
          sum = a3 - b3 - c3;
          if (sum == n) {
            return new Solution(Sign.PLUS, a, Sign.MINUS, b, Sign.MINUS, c);
          }

          // - + +
          sum = - a3 + b3 + c3;
          if (sum == n) {
            return new Solution(Sign.MINUS, a, Sign.PLUS, b, Sign.PLUS, c);
          }

          // - + -
          sum = - a3 + b3 - c3;
          if (sum == n) {
            return new Solution(Sign.MINUS, a, Sign.PLUS, b, Sign.MINUS, c);
          }

          // - - +
          sum = - a3 - b3 + c3;
          if (sum == n) {
            return new Solution(Sign.MINUS, a, Sign.MINUS, b, Sign.PLUS, c);
          }
        }
      }
    }

    return null;
  }

  // optimized solution:
  // x3 + y3 = (x+y)(x2+y2-xy)

  // demo

  private interface SolutionFinder {
    Solution find(int n);
  }

  private static void demo(int n, SolutionFinder f) {
    final int nineResidue = n % 9;
    if (nineResidue == 4 || nineResidue == 5) {
      System.out.println("solution does not exist / could not be found for n=" + n);
      return;
    }

    final Solution s = f.find(n);
    if (s != null) {
      System.out.println(String.format("%3d = %s", n, s));
    } else {
      System.out.println("no solution found for n=" + n);
    }
  }

  public static void main(String[] args) {
    for (int i = 1; i < 100; ++i) {
      demo(i, Cube3Sum::bruteForceFind);
    }

    System.out.println("---");
  }
}
