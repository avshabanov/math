package problems.leet100.challenges.c2020_04.w1;

import java.util.*;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/528/week-1/3288/
 * <p>
 * Given an array of strings, group anagrams together.
 *
 * Example:
 *
 * Input: ["eat", "tea", "tan", "ate", "nat", "bat"],
 * Output:
 * [
 *   ["ate","eat","tea"],
 *   ["nat","tan"],
 *   ["bat"]
 * ]
 * Note:
 *
 * All inputs will be in lowercase.
 * The order of your output does not matter.
 * </p>
 */
public class GroupAnagramsSolution {

  public static void main(String[] args) {
    System.out.println("Groups=" + groupAnagrams(new String[] {
        "eat", "tea", "tan", "ate", "nat", "bat"
    }));
  }

  private static List<List<String>> groupAnagrams(String[] strs) {
    final Map<CharKey, List<String>> groups = new HashMap<>();
    for (final String s : strs) {
      CharKey key = new CharKey(s);
      final List<String> val = groups.computeIfAbsent(key, (ignored) -> new ArrayList<>());
      val.add(s);
    }
    return new ArrayList<>(groups.values());
  }

  private static final class CharKey {
    final char[] chars;

    public CharKey(String s) {
      this.chars = s.toCharArray();
      Arrays.sort(chars);
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof CharKey)) return false;

      CharKey charKey = (CharKey) o;

      return Arrays.equals(chars, charKey.chars);
    }

    @Override
    public int hashCode() {
      return Arrays.hashCode(chars);
    }
  }
}
