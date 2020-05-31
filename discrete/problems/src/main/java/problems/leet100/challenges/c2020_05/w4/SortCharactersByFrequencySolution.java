package problems.leet100.challenges.c2020_05.w4;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/537/week-4-may-22nd-may-28th/3337/
 * <p>Given a string, sort it in decreasing order based on the frequency of characters.</p>
 */
public class SortCharactersByFrequencySolution {

  private static String frequencySort(String s) {
    final Map<Character, Integer> frequencies = new HashMap<>();
    for (int i = 0; i < s.length(); ++i) {
      frequencies.compute(s.charAt(i), (k, v) -> v == null ? 1 : (v + 1));
    }

    final List<Map.Entry<Character, Integer>> entries = frequencies.entrySet().stream()
        .sorted((l, r) -> r.getValue().compareTo(l.getValue())).collect(Collectors.toList());

    final StringBuilder sb = new StringBuilder(s.length());
    for (final Map.Entry<Character, Integer> e : entries) {
      IntStream.range(0, e.getValue()).forEach(i -> sb.append(e.getKey()));
    }
    return sb.toString();
  }
}
