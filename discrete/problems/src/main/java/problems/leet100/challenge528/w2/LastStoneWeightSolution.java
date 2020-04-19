package problems.leet100.challenge528.w2;

import java.util.TreeSet;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/529/week-2/3297/
 */
public class LastStoneWeightSolution {

  public static void main(String[] args) {
    int w = lastStoneWeight(new int[] {2,7,4,1,8,1});
    //int w = lastStoneWeight(new int[] {2,2});
    System.out.println("w = " + w);
  }

  private static int lastStoneWeight(int[] stones) {
    final TreeSet<Stone> set = new TreeSet<>();
    for (int i = 0; i < stones.length; ++i) {
      set.add(new Stone(stones[i], i));
    }

    while (set.size() > 1) {
      final Stone a = set.pollLast();
      final Stone b = set.pollLast();
      assert a != null && b != null;
      final int c = Math.abs(a.value - b.value);
      if (c > 0) {
        set.add(new Stone(c, a.ordinal));
      }
    }
    return set.isEmpty() ? 0 : set.first().value;
  }

  static final class Stone implements Comparable<Stone> {
    final int value;
    final int ordinal;

    public Stone(int value, int ordinal) {
      this.value = value;
      this.ordinal = ordinal;
    }

    @Override
    public int compareTo(Stone o) {
      final int r = Integer.compare(value, o.value);
      return r != 0 ? r : Integer.compare(ordinal, o.ordinal);
    }
  }
}
