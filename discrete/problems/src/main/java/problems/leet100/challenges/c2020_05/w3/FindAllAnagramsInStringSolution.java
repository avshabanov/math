package problems.leet100.challenges.c2020_05.w3;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/536/week-3-may-15th-may-21st/3332/
 * <p>Given a string s and a non-empty string p, find all the start indices of p's anagrams in s.
 * Strings consists of lowercase English letters only and the length of both strings s and p will not be larger
 * than 20,100.
 * The order of output does not matter.</p>
 */
public class FindAllAnagramsInStringSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println(findAnagrams("cbaebabacd", "abc"));
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      System.out.println(findAnagrams("aaaaaaa", "aaa"));
    }
  }

  private static List<Integer> findAnagrams(String s, String p) {
    // compute pattern char frequencies
    final Map<Character, Integer> patternFreq = new HashMap<>();
    for (int i = 0; i < p.length(); ++i) {
      patternFreq.compute(p.charAt(i), (k, v) -> 1 + (v == null ? 0 : v));
    }

    final List<Integer> anagramPos = new ArrayList<>();

    // compute initial frequency map off of first len(pattern) chars in the source string
    final Map<Character, Integer> itFreq = new HashMap<>();
    for (int i = 0; i < Math.min(p.length(), s.length()); ++i) {
      itFreq.compute(s.charAt(i), (k, v) -> 1 + (v == null ? 0 : v));
      if (itFreq.equals(patternFreq)) {
        anagramPos.add(0);
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
        anagramPos.add(i - p.length() + 1);
      }
    }
    return anagramPos;
  }
}
