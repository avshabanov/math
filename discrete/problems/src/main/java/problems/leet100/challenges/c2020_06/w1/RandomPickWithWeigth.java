package problems.leet100.challenges.c2020_06.w1;

import java.util.Arrays;
import java.util.Map;
import java.util.TreeMap;
import java.util.concurrent.ThreadLocalRandom;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/539/week-1-june-1st-june-7th/3351/
 * <p>Given an array w of positive integers, where w[i] describes the weight of index i,
 * write a function pickIndex which randomly picks an index in proportion to its weight.
 * </p><p>
 * Note:
 * 1 <= w.length <= 10000
 * 1 <= w[i] <= 10^5
 * pickIndex will be called at most 10000 times.</p>
 */
public class RandomPickWithWeigth {

  public static final class Demo1 {
    public static void main(String[] args) {
      final Solution s = new Solution(new int[] {1, 3});
      System.out.print("s =");
      for (int i = 0; i < 10; ++i) {
        final int n = s.pickIndex();
        System.out.print(" " + n);
      }
      System.out.println();
      System.out.println("---");
    }
  }

  private static final class Solution {
    final long limit;
    final TreeMap<Long, Integer> weigthToIndexMap = new TreeMap<>();

    public Solution(int[] w) {
      this.limit = Arrays.stream(w).sum();
      long weigth = 0;
      for (int i = 0; i < w.length; ++i) {
        weigthToIndexMap.put(weigth, i);
        weigth += w[i];
      }
    }

    public int pickIndex() {
      final long rand = ThreadLocalRandom.current().nextLong(limit);
      final Map.Entry<Long, Integer> e = weigthToIndexMap.floorEntry(rand);
      if (e == null) {
        throw new IllegalStateException();
      }
      return e.getValue();
    }
  }
}
