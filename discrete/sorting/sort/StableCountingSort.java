import util.CountingSortKeyProvider;
import util.SortUtil;

import java.util.List;

/**
 * Special kind of sorting optimized for small integers: https://en.wikipedia.org/wiki/Counting_sort
 * This is a stable sort algorithm.
 *
 * @author Alexander Shabanov
 */
public final class StableCountingSort {
  public static void main(String[] args) {
    SortUtil.runStandardFixture(StableCountingSort::inplaceCountingSort);
  }

  public static void inplaceCountingSort(int[] input) {
    final int[] output = new int[input.length];

    stableCountingSort(SortUtil.asMutableList(input), SortUtil.asMutableList(output),
        SortUtil.getCountingSortKeyProvider(input));

    System.arraycopy(output, 0, input, 0, input.length);
  }

  /**
   * Performs counting sort. This algorithm is efficient for small values of <code>max</code> parameter.
   *
   * @param input List, containing elements from zero, inclusive to <code>max</code>, exclusive
   * @param output List, that will hold sorted element. Should not match <code>input</code>.
   * @param keyProvider An interface, aware of how to fold a value into the integer key
   */
  @SuppressWarnings("ForLoopReplaceableByForEach")
  public static <T> void stableCountingSort(List<T> input, List<T> output, CountingSortKeyProvider<T> keyProvider) {
    final int[] counters = new int[keyProvider.getMaximumValue()];
    final int size = input.size();

    // calculate frequency of each value in a given array (i.e. histogram), so initially
    // 'indexes' array contains just a values of how many times each element occurs in the given array
    for (int i = 0; i < size; ++i) {
      counters[keyProvider.getKey(input.get(i))] += 1;
    }

    // calculate the starting index for each element, so that 'indexes' array will hold
    // relative offset for each element in a given array
    {
      int startIndex = 0;
      for (int i = 0; i < counters.length; ++i) {
        final int frequency = counters[i];
        counters[i] = startIndex;
        startIndex += frequency;
      }
    }

    // then rearrange each value in a given array, preserving an order of elements
    for (int i = 0; i < size; ++i) {
      final T value = input.get(i);
      final int key = keyProvider.getKey(value);
      output.set(counters[key], value);
      counters[key] += 1;
    }
  }
}
