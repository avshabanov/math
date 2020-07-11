package problems.leet100.challenges.c2020_06.w2;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/540/week-2-june-8th-june-14th/3354/
 */
public class PowerOfTwo {

  private static boolean isPowerOfTwo(int n) {
    if (n <= 0) {
      return false;
    }
    return (n & (n - 1)) == 0;
  }
}
