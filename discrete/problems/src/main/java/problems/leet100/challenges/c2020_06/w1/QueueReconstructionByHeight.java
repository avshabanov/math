package problems.leet100.challenges.c2020_06.w1;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/539/week-1-june-1st-june-7th/3352/
 * <p>Suppose you have a random list of people standing in a queue.
 * Each person is described by a pair of integers (h, k), where h is the height of the person and k is the number of
 * people in front of this person who have a height greater than or equal to h.
 * Write an algorithm to reconstruct the queue.
 *
 * Note:
 * The number of people is less than 1,100.
 *
 *
 * Example
 *
 * Input:
 * [[7,0], [4,4], [7,1], [5,0], [6,1], [5,2]]
 *
 * Output:
 * [[5,0], [7,0], [5,2], [6,1], [4,4], [7,1]]</p>
 */
public class QueueReconstructionByHeight {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(new int[][] {
          {7,0}, {4,4}, {7,1}, {5,0}, {6,1}, {5,2}
      });
    }
  }

  private static String asString(int[][] people) {
    return Arrays.stream(people).map(Arrays::toString).collect(Collectors.joining(", "));
  }

  private static void demo(int[][] people) {
    System.out.printf("Input: %s\nOutput: %s\n", asString(people), asString(UnoptScan.reconstructQueue(people)));
  }

  private static final class UnoptScan {
    static int[][] reconstructQueue(int[][] people) {
      final List<Ent> ents = Arrays.stream(people).map(Ent::new).sorted().collect(Collectors.toList());
      final List<int[]> result = new ArrayList<>(people.length);

      while (result.size() != people.length) {
        int numIncremented = 0;
        for (int i = 0; i < ents.size(); ++i) {
          final Ent e = ents.get(i);
          if (e.kCounter == 0) {
            ++numIncremented;
            result.add(e.toPair());
            e.kCounter = -1;
            recursiveAdjust(ents, result, i);
          }
        }
        if (numIncremented == 0) {
          throw new IllegalStateException();
        }
      }

      return result.toArray(new int[result.size()][]);
    }

    private static void recursiveAdjust(List<Ent> ents, List<int[]> result, int toIndex) {
      for (int j = 0; j < toIndex; ++j) {
        final Ent e = ents.get(j);
        if (e.kCounter < 0) {
          continue;
        } else if (e.kCounter == 0) {
          throw new IllegalStateException("e.kCounter == 0");
        }

        final int newK = e.kCounter - 1;
        if (newK == 0) {
          result.add(e.toPair());
          recursiveAdjust(ents, result, j);
          e.kCounter = -1;
        } else {
          e.kCounter = newK;
        }
      }
    }

    private static final class Ent implements Comparable<Ent> {
      final int h;
      final int k;
      int kCounter;

      Ent(int[] origin) {
        h = origin[0];
        k = origin[1];
        kCounter = k;
      }

      int[] toPair() {
        return new int[] {h, k};
      }

      @Override public int compareTo(Ent o) {
        if (h == o.h) {
          return Integer.compare(o.k, k);
        }
        return Integer.compare(h, o.h);
      }
    }
  }


}
