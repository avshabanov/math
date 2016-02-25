import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Shabanov
 */
public final class ArrayDiffExample {

  public static void main(String[] args) {
    demo(Arrays.asList(1, 2, 3, 5, 6, 8, 9, 11, 12, 13), 10);
    demo(Arrays.asList(1, 2, 3, 5, 6, 8, 9, 11, 12, 13), 3);
    demo(Arrays.asList(1, 3, 5, 7, 9, 11, 13, 15, 17, 19), 2);
    demo(Arrays.asList(10, 15, 20), 7);
  }

  private static void demo(List<Integer> arr, int k) {
    Collections.sort(arr);

    final List<Pair> pairs = nonOptimizedGetDiff(arr, k);
    final List<Pair> optPairs = optimizedGetDiff(arr, k);
    if (!pairs.equals(optPairs)) {
      throw new AssertionError("Error for arr=" + arr);
    }
    System.out.println("arr=" + arr + ", k=" + k + ", pairs=" + pairs);
  }

  private static List<Pair> nonOptimizedGetDiff(List<Integer> arr, int k) {
    final List<Pair> result = new ArrayList<>();

    for (int i = 0; i < arr.size(); ++i) {
      for (int j = i + 1; j < arr.size(); ++j) {
        final int diff = arr.get(j) - arr.get(i);
        if (diff == k) {
          result.add(new Pair(arr.get(i), arr.get(j)));
        } else if (diff > k) {
          break;
        }
      }
    }

    return result;
  }

  private static List<Pair> optimizedGetDiff(List<Integer> arr, int k) {
    final List<Pair> result = new ArrayList<>();

    int prevIndex = -1;
    for (int i = 0; i < arr.size(); ++i) {
      for (int j = Math.max(prevIndex, i + 1); j < arr.size(); ++j) {
        final int diff = arr.get(j) - arr.get(i);
        if (diff == k) {
          result.add(new Pair(arr.get(i), arr.get(j)));
        } else if (diff > k) {
          prevIndex = j;
          break;
        }
      }
    }

    return result;
  }

  private static final class Pair {
    final int first;
    final int second;

    public Pair(int first, int second) {
      this.first = first;
      this.second = second;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof Pair)) return false;

      Pair pair = (Pair) o;

      if (first != pair.first) return false;
      return second == pair.second;

    }

    @Override
    public int hashCode() {
      int result = first;
      result = 31 * result + second;
      return result;
    }

    @Override
    public String toString() {
      return "[" + first + ", " + second + ']';
    }
  }

}
