import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static java.util.Arrays.asList;
import static java.util.Collections.emptyList;
import static java.util.Collections.singletonList;
import static java.util.Collections.sort;

/**
 * Sample run:
 * <pre>
 * The ways to represent sum=1 with coins=[] are: []
 * The ways to represent sum=1 with coins=[2] are: []
 * The ways to represent sum=1 with coins=[1] are: [[1]]
 * The ways to represent sum=7 with coins=[4, 1, 5] are: []
 * The ways to represent sum=8 with coins=[4, 2, 1, 5, 3] are: [[1, 3, 4], [1, 2, 5], [3, 5]]
 * The ways to represent sum=10 with coins=[4, 4, 2, 5, 3] are: [[2, 4, 4], [2, 3, 5]]
 * The ways to represent sum=16 with coins=[1, 3, 10, 15] are: [[1, 15]]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class DenomExample {

  public static void main(String[] args) {
    demo(1, emptyList());
    demo(1, singletonList(2));
    demo(1, singletonList(1));
    demo(7, asList(4, 1, 5));
    demo(8, asList(4, 2, 1, 5, 3));
    demo(10, asList(4, 4, 2, 5, 3));
    demo(16, asList(1, 3, 10, 15));
  }

  public static void demo(int sum, List<Integer> coins) {
    System.out.println("The ways to represent sum=" + sum + " with coins=" + coins +
        " are: " + represent(sum, coins));
  }

  public static Set<List<Integer>> represent(int sum, List<Integer> coins) {
    final Finder finder = new Finder(sum, coins);
    finder.find(0, 0);
    return finder.result;
  }

  public static final class Finder {
    final Set<List<Integer>> result = new HashSet<>();
    final List<Integer> current = new ArrayList<>();
    final int sum;
    final List<Integer> coins;

    public Finder(int sum, List<Integer> coins) {
      this.sum = sum;
      this.coins = coins;
    }

    public void find(int currentSum, int pos) {
      if (currentSum == sum) {
        final List<Integer> copyCurrent = new ArrayList<>(current);
        sort(copyCurrent);
        result.add(copyCurrent);
        return;
      } else if (currentSum > sum) {
        return;
      }

      final int last = current.size();
      for (int i = pos; i < coins.size(); ++i) {
        final int coin = coins.get(i);
        current.add(coin);
        find(currentSum + coin, i + 1);
        current.remove(last);
      }
    }
  }
}
