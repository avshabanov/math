package problems.leet100.challenges.c2020_05.w1;

import java.util.HashMap;
import java.util.Map;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/534/week-1-may-1st-may-7th/3318/
 * <p>Given an arbitrary ransom note string and another string containing letters from all the magazines, write a
 * function that will return true if the ransom note can be constructed from the magazines;
 * otherwise, it will return false.
 *
 * Each letter in the magazine string can only be used once in your ransom note.
 *
 * Note:
 * You may assume that both strings contain only lowercase letters.</p>
 */
public class RansomNoteSolution {

  private static boolean canConstruct(String ransomNote, String magazine) {
    final Map<Character, Integer> charCount = new HashMap<>(Math.min(1000, magazine.length() * 2));
    for (int i = 0; i < magazine.length(); ++i) {
      charCount.compute(magazine.charAt(i), (k, v) -> {
        if (v != null) {
          return v + 1;
        }
        return 1;
      });
    }

    for (int i = 0; i < ransomNote.length(); ++i) {
      final int count = charCount.compute(ransomNote.charAt(i), (k, v) -> {
        if (v == null) {
          return -1;
        }
        return v - 1;
      });
      if (count < 0) {
        return false;
      }
    }

    return true;
  }
}
