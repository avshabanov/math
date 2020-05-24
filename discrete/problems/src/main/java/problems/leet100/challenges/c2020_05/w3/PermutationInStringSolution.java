package problems.leet100.challenges.c2020_05.w3;

import java.util.HashMap;
import java.util.Map;

/**
 * https://leetcode.com/explore/featured/card/may-leetcoding-challenge/536/week-3-may-15th-may-21st/3333/
 * <p>Given two strings s1 and s2, write a function to return true if s2 contains the permutation of s1.
 * In other words, one of the first string's permutations is the substring of the second string.</p>
 * <p>Note:
 * The input strings only contain lower case letters.
 * The length of both given strings is in range [1, 10,000].</p>
 */
public class PermutationInStringSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println(checkInclusion("ab", "eidbaooo"));
      System.out.println(checkInclusion("ba", "eidboaoo"));
    }
  }

  private static boolean checkInclusion(String p, String s) {
    // compute pattern char frequencies
    final Map<Character, Integer> patternFreq = new HashMap<>();
    for (int i = 0; i < p.length(); ++i) {
      patternFreq.compute(p.charAt(i), (k, v) -> 1 + (v == null ? 0 : v));
    }

    // compute initial frequency map off of first len(pattern) chars in the source string
    final Map<Character, Integer> itFreq = new HashMap<>();
    for (int i = 0; i < Math.min(p.length(), s.length()); ++i) {
      itFreq.compute(s.charAt(i), (k, v) -> 1 + (v == null ? 0 : v));
      if (itFreq.equals(patternFreq)) {
        return true;
      }
    }

    // update pattern for the remaining portion of source string
    for (int i = p.length(); i < s.length(); ++i) {
      itFreq.compute(s.charAt(i), (k, v) -> 1 + (v == null ? 0 : v));
      itFreq.compute(s.charAt(i - p.length()), (k, v) -> {
        @SuppressWarnings("ConstantConditions") final int newFreq = v - 1;
        return newFreq == 0 ? null : newFreq;
      });
      if (itFreq.equals(patternFreq)) {
        return true;
      }
    }
    return false;
  }

  public class AlternativeSolution { /* courtesy of leetcode */
    public boolean checkInclusion(String s1, String s2) {
      if (s1.length() > s2.length())
        return false;
      HashMap < Character, Integer > s1map = new HashMap < > ();
      for (int i = 0; i < s1.length(); i++)
        s1map.put(s1.charAt(i), s1map.getOrDefault(s1.charAt(i), 0) + 1);
      for (int i = 0; i <= s2.length() - s1.length(); i++) {
        HashMap < Character, Integer > s2map = new HashMap < > ();
        for (int j = 0; j < s1.length(); j++) {
          s2map.put(s2.charAt(i + j), s2map.getOrDefault(s2.charAt(i + j), 0) + 1);
        }
        if (matches(s1map, s2map))
          return true;
      }
      return false;
    }
    public boolean matches(HashMap < Character, Integer > s1map, HashMap < Character, Integer > s2map) {
      for (char key: s1map.keySet()) {
        if (s1map.get(key) - s2map.getOrDefault(key, -1) != 0)
          return false;
      }
      return true;
    }
  }
}
