package problems.leet100.challenges.c2020_05.w2;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/535/week-2-may-8th-may-14th/3324/
 * <p>Given a positive integer num, write a function which returns True if num is a perfect square else False.
 *
 * Note: Do not use any built-in library function such as sqrt.</p>
 */
public class ValidPerfectSquareSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      for (int i = 0; i < 10; ++i) {
        System.out.printf("%d %s a perfect square\n", i, isPerfectSquare(i) ? "is" : "is not");
      }

      System.out.printf("256 ~ %s\n", isPerfectSquare(256));
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      System.out.println(isPerfectSquare(2147483647));
    }
  }

  private static boolean isPerfectSquare(int num) {
    // use binary search
    int left = 0;
    int right = num;
    while (right >= left) {
      final int med = (int) (((long) left + right) / 2);
      final long square = ((long) med) * med;
      if (square > (long) num) {
        right = med - 1;
      } else if (square < num) {
        left = med + 1;
      } else {
        return true;
      }
    }
    return false;
  }
}
