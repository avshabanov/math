package problems.leet100.challenges.c2020_06.w1;

import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/539/week-1-june-1st-june-7th/3349/
 * <p>There are 2N people a company is planning to interview. The cost of flying the i-th person to city A
 * is costs[i][0], and the cost of flying the i-th person to city B is costs[i][1].
 * Return the minimum cost to fly every person to a city such that exactly N people arrive in each city.</p>
 * <p>Note:
 * 1 <= costs.length <= 100
 * It is guaranteed that costs.length is even.
 * 1 <= costs[i][0], costs[i][1] <= 1000</p>
 */
public class TwoCitySchedulingSolution {

  private static final class Eager {
    private static int twoCitySchedCost(int[][] costs) {
      final List<DiffElem> diff = Arrays.stream(costs).map(DiffElem::new)
          .sorted(Comparator.comparingInt(l -> l.diff)).collect(Collectors.toList());
      int result = 0;
      final int offset = costs.length / 2;
      for (int i = 0; i < offset; ++i) {
        result += (diff.get(i).pair[0] + diff.get(i + offset).pair[1]);
      }
      return result;
    }

    private static final class DiffElem {
      final int[] pair;
      final int diff;

      public DiffElem(int[] pair) {
        this.pair = pair;
        this.diff = pair[0] - pair[1];
      }
    }
  }

  private static final class Bruteforce {
    private static int twoCitySchedCost(int[][] costs) {
      final MinFinder s = new MinFinder(costs);
      s.findMin(0);
      return s.result;
    }

    private static final class MinFinder {
      int result = Integer.MAX_VALUE;
      int current = 0;
      final int[][] costs;

      public MinFinder(int[][] costs) {
        this.costs = costs;
      }

      private void findMin(int next) {
        if (next == costs.length) {
          result = Math.min(result, current);
          return;
        }

        current += costs[next][0];
        findMin(next + 1);
        current -= costs[next][0];

        current += costs[next][1];
        findMin(next + 1);
        current -= costs[next][1];
      }
    }
  }
}
