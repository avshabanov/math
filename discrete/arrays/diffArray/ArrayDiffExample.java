import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Shabanov
 */
public final class ArrayDiffExample {

  public static void main(String[] args) {
    demo(Arrays.asList(1, 2, 3, 5, 6, 8, 9, 11, 12, 13), 3);
  }

  private static void demo(List<Integer> arr, int k) {
    Collections.sort(arr);

    final List<Pair> pairs = nonOptimizedGetDiff(arr, k);
    System.out.println("arr=" + arr + ", k=" + k + ", pairs=" + pairs);
  }

  private static List<Pair> nonOptimizedGetDiff(List<Integer> arr, int k) {
    final List<Pair> result = new ArrayList<>();

    for (int i = 0; i < arr.size(); ++i) {
      for (int j = i + 1; j < arr.size(); ++j) {
        final int diff = arr.get(j) - arr.get(i);
        if (diff == k) {
          result.add(new Pair(arr.get(i), arr.get(j)));
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
    public String toString() {
      return "[" + first + ", " + second + ']';
    }
  }

}
