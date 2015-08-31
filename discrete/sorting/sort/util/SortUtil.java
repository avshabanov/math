package util;

import java.util.AbstractList;
import java.util.Arrays;
import java.util.List;

/**
 * Utility class for sorting demos
 */
public final class SortUtil {
  private SortUtil() {}

  public interface InplaceSortAlgorithm {
    void sort(int[] arr);
  }

  public static void sortAndPrint(InplaceSortAlgorithm algorithm, int[] arr) {
    final int[] expected = Arrays.copyOf(arr, arr.length);
    Arrays.sort(expected);

    System.out.println("Unsorted arr=" + Arrays.toString(arr));
    algorithm.sort(arr);

    if (!Arrays.equals(expected, arr)) {
      throw new AssertionError("Sort algorithm failed: expected=" + Arrays.toString(expected) +
          ", actual=" + Arrays.toString(arr));
    }

    System.out.println("Sorted   arr=" + Arrays.toString(arr));
    System.out.println("===");
  }

  public static void runStandardFixture(InplaceSortAlgorithm algorithm) {
    sortAndPrint(algorithm, new int[]{33, 48, 25, 12, 36, 19, 45});
    sortAndPrint(algorithm, new int[]{1, 2, 3, 4, 5, 6, 7, 8, 9});
    sortAndPrint(algorithm, new int[]{9, 8, 7, 6, 5, 4, 3, 2, 1});
    sortAndPrint(algorithm, new int[]{3, 1, 3, 1, 5, 5, 3, 3});
    sortAndPrint(algorithm, new int[]{3, 2, 1});
    sortAndPrint(algorithm, new int[]{2, 1});
    sortAndPrint(algorithm, new int[]{1, 2});
    sortAndPrint(algorithm, new int[]{1});
    sortAndPrint(algorithm, new int[]{});
  }

  public static List<Integer> asMutableList(int[] array) {
    return new BoxedIntList(array);
  }

  public static CountingSortKeyProvider<Integer> getCountingSortKeyProvider(int[] input) {
    // This should normally be performed by counting sort caller
    int max = 0;
    for (final int val : input) {
      max = Math.max(max, val);
    }

    final int maxElement = max + 1;

    return new CountingSortKeyProvider<Integer>() {
      @Override
      public int getMaximumValue() {
        return maxElement;
      }

      @Override
      public int getKey(Integer value) {
        return value;
      }
    };
  }

  //
  // Private
  //

  private static final class BoxedIntList extends AbstractList<Integer> {
    private final int[] input;

    public BoxedIntList(int[] input) {
      this.input = input;
    }

    @Override
    public Integer get(int index) {
      return input[index];
    }

    @Override
    public Integer set(int index, Integer element) {
      if (index < 0 || index >= input.length) {
        throw new IndexOutOfBoundsException("index=" + index + " is out of bounds");
      }
      final int prev = input[index];
      input[index] = element;
      return prev;
    }

    @Override
    public int size() {
      return input.length;
    }
  }
}
