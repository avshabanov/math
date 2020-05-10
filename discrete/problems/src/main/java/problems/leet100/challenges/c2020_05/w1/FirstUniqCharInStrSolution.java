package problems.leet100.challenges.c2020_05.w1;

import java.util.HashMap;
import java.util.Map;

/**
 * https://leetcode.com/explore/featured/card/may-leetcoding-challenge/534/week-1-may-1st-may-7th/3320/
 * <p>Given a string, find the first non-repeating character in it and return it's index.
 * If it doesn't exist, return -1.</p>
 */
public class FirstUniqCharInStrSolution {

  private static int firstUniqChar(String s) {
    final Map<Character, Integer> m = new HashMap<>();
    for (int i = 0; i < s.length(); ++i) {
      m.compute(s.charAt(i), (k, v) -> v == null ? 1 : v + 1);
    }

    for (int i = 0; i < s.length(); ++i) {
      if (1 == m.get(s.charAt(i))) {
        return i;
      }
    }

    return -1;
  }
}
