package problems.leet100.challenges.c2020_06.w2;

import java.util.*;
import java.util.concurrent.ThreadLocalRandom;
import java.util.stream.IntStream;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/540/week-2-june-8th-june-14th/3358/
 * <p>Design a data structure that supports all following operations in average O(1) time.
 *
 * insert(val): Inserts an item val to the set if not already present.
 * remove(val): Removes an item val from the set if present.
 * getRandom: Returns a random element from current set of elements. Each element must have the same probability of being returned.
 * Example:
 *
 * // Init an empty set.
 * RandomizedSet randomSet = new RandomizedSet();
 *
 * // Inserts 1 to the set. Returns true as 1 was inserted successfully.
 * randomSet.insert(1);
 *
 * // Returns false as 2 does not exist in the set.
 * randomSet.remove(2);
 *
 * // Inserts 2 to the set, returns true. Set now contains [1,2].
 * randomSet.insert(2);
 *
 * // getRandom should return either 1 or 2 randomly.
 * randomSet.getRandom();
 *
 * // Removes 1 from the set, returns true. Set now contains [2].
 * randomSet.remove(1);
 *
 * // 2 was already in the set, so return false.
 * randomSet.insert(2);
 *
 * // Since 2 is the only number in the set, getRandom always return 2.
 * randomSet.getRandom();</p>
 */
public class InsertDeleteGetRandomO1 {

  public static void main(String[] args) {
    final RandomizedSet s = new RandomizedSet();
    s.insert(10);
    s.insert(20);
    s.insert(30);
    s.remove(10);

    final String arr = Arrays.toString(IntStream.range(0, 10).map((n) -> s.getRandom()).toArray());
    System.out.println(arr);
  }

  private static final class RandomizedSet {
    private final Map<Integer, Integer> valToPos = new HashMap<>();
    private final List<Integer> keys = new ArrayList<>();

    /** Initialize your data structure here. */
    public RandomizedSet() {

    }

    /** Inserts a value to the set. Returns true if the set did not already contain the specified element. */
    public boolean insert(int val) {
      if (valToPos.containsKey(val)) {
        return false;
      }

      valToPos.put(val, keys.size());
      keys.add(val);
      return true;
    }

    /** Removes a value from the set. Returns true if the set contained the specified element. */
    public boolean remove(int val) {
      if (!valToPos.containsKey(val)) {
        return false;
      }
      final int pos = valToPos.remove(val);
      final int last = keys.size() - 1;
      if (pos != last) {
        final int lastVal = keys.get(last);
        valToPos.put(lastVal, pos);
        keys.set(pos, lastVal);
      }
      keys.remove(last);
      return true;
    }

    /** Get a random element from the set. */
    public int getRandom() {
      if (keys.isEmpty()) {
        throw new IllegalStateException();
      }
      return keys.get(keys.size() == 1 ? 0 : ThreadLocalRandom.current().nextInt(0, keys.size()));
    }
  }
}
