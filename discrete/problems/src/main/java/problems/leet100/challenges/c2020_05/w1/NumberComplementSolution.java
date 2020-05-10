package problems.leet100.challenges.c2020_05.w1;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/534/week-1-may-1st-may-7th/3319/
 * <p>Given a positive integer, output its complement number.
 * The complement strategy is to flip the bits of its binary representation.
 *
 * The given integer is guaranteed to fit within the range of a 32-bit signed integer.
 * You could assume no leading zero bit in the integer’s binary representation.</p>
 */
public class NumberComplementSolution {

  public static void main(String[] args) {
    System.out.printf("Input: %d\nOutput: %d\n", 5, findComplement(5));
    System.out.printf("Input: %d\nOutput: %d\n", 7, findComplement(7));
  }

  private static int findComplement(int num) {
    int result = 0;
    int flag = 1;
    while (num > 0) {
      if ((num & 1) == 0) {
        result |= flag;
      }
      flag = flag << 1;
      num = num >> 1;
    }

    return result;
  }
}
