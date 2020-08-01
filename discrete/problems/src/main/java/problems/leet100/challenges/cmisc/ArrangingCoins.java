package problems.leet100.challenges.cmisc;

/**
 * https://leetcode.com/explore/challenge/card/july-leetcoding-challenge/544/week-1-july-1st-july-7th/3377/
 *
 * <p>You have a total of n coins that you want to form in a staircase shape, where every k-th row must have exactly k coins.
 * Given n, find the total number of full staircase rows that can be formed.
 * n is a non-negative integer and fits within the range of a 32-bit signed integer.</p>
 */
public class ArrangingCoins {

  public static void main(String[] args) {
    System.out.println("r(3) = " + arrangeCoins(3));
    System.out.println("r(4) = " + arrangeCoins(4));
    System.out.println("r(5) = " + arrangeCoins(5));
    System.out.println("r(6) = " + arrangeCoins(6));
    System.out.println("r(7) = " + arrangeCoins(7));
  }

  // math
  int arrangeCoins2(int n) {
    return (int) (Math.sqrt(2 * (long)n + 0.25) - 0.5);
  }

  // binary search
  private static int arrangeCoins(int n) {
    final long bound = 2L * n;
    long left = 1;
    long right = n;
    while (right >= left) {
      final long median = (left + right) / 2;
      final long product = median * (median + 1);
      if (product > bound) {
        right = median - 1;
        continue;
      }

      left = median + 1;
      if (product == bound) {
        return (int) median;
      }
    }

    return (int) (left - 1);
  }
}
