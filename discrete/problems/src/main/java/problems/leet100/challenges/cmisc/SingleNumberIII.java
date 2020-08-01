package problems.leet100.challenges.cmisc;

import java.util.HashMap;
import java.util.Map;

/**
 * Single Number III
 * Given an array of numbers nums, in which exactly two elements appear only once and all the other elements appear
 * exactly twice. Find the two elements that appear only once.
 */
public class SingleNumberIII {

  private static int[] singleNumber(int[] nums) {
    final Map<Integer, Integer> m = new HashMap<>(nums.length);
    for (int n : nums) {
      m.compute(n, (k, v) -> (v == null ? 0 : v) + 1);
    }
    return m.entrySet().stream().filter(e -> e.getValue() == 1)
        .mapToInt(Map.Entry::getKey).toArray();
  }
}
