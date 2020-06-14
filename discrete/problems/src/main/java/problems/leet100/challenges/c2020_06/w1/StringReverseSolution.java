package problems.leet100.challenges.c2020_06.w1;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/539/week-1-june-1st-june-7th/3350/
 */
public class StringReverseSolution {

  void reverseString(char[] s) {
    int half = s.length / 2;
    for (int i = 0; i < half; ++i) {
      final char ch = s[i];
      final int opposite = s.length - i - 1;
      s[i] = s[opposite];
      s[opposite] = ch;
    }
  }
}
