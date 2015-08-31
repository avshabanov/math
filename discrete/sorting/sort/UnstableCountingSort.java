import util.CountingSortKeyProvider;
import util.SortUtil;

import java.util.List;

/**
 * Unstable counting sort that can do an inplace sorting of an input array.
 *
 * @author Alexander Shabanov
 */
public class UnstableCountingSort {

  public static void main(String[] args) {
    SortUtil.runStandardFixture(new SortUtil.InplaceSortAlgorithm() {
      @Override
      public void sort(int[] arr) {
        inplaceCountingSort(arr);
      }
    });
  }

  public static void inplaceCountingSort(int[] input) {
    unstableCountingSort(SortUtil.asMutableList(input), SortUtil.getCountingSortKeyProvider(input));
  }

  @SuppressWarnings("ForLoopReplaceableByForEach")
  public static <T> void unstableCountingSort(List<T> input, CountingSortKeyProvider<T> keyProvider) {
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
    for (int i = size - 1; i >= 0; --i) {
      T value = input.get(i);
      int key = keyProvider.getKey(value);

      int j = counters[key];
      System.out.println("  [COUNTING] i=" + i + ", j=" + j + ", value=" + value);
      if (j < i) {
        do {
          ++counters[key];
          value = input.set(j, value);
          key = keyProvider.getKey(value);
          j = counters[key];
          System.out.println("    [COUNTING] next=" + j + ", newValue=" + value);
        } while (j < i);

        input.set(i, value);
      }
    }

    System.out.println(" (TERM)\n");
  }
}
