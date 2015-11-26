import java.util.Arrays;

/**
 * Sample radix sort:
 *
 * <pre>
 * Unsorted = [100, 200, 300]
 * Sorted   = [100, 200, 300]
 * ---
 * Unsorted = [550, 460, 280]
 * Sorted   = [280, 460, 550]
 * ---
 * Unsorted = [611, 811, 911, 411, 511, 211, 311, 711, 111]
 * Sorted   = [111, 211, 311, 411, 511, 611, 711, 811, 911]
 * ---
 * Unsorted = [222, 222, 444, 333, 333, 222, 111, 222, 111]
 * Sorted   = [111, 111, 222, 222, 222, 222, 333, 333, 444]
 * ---
 * Unsorted = [221, 222, 400, 332, 330, 210, 120, 220, 110]
 * Sorted   = [110, 120, 210, 220, 221, 222, 330, 332, 400]
 * ---
 * </pre>
 */
public final class RadixSort {
  public static void main(String[] args) {
    performSort("100", "200", "300");
    performSort("550", "460", "280");
    performSort("611", "811", "911", "411", "511", "211", "311", "711", "111");
    performSort("222", "222", "444", "333", "333", "222", "111", "222", "111");
    performSort("221", "222", "400", "332", "330", "210", "120", "220", "110");
  }

  //
  // Private
  //

  private static void performSort(String... elems) {
    System.out.println("Unsorted = " + Arrays.toString(elems));
    radixSort(elems);
    System.out.println("Sorted   = " + Arrays.toString(elems));
    System.out.println("---");
  }

  private static final int DIGITS = 3; // total count of digits/string
  private static final int DIGIT_MAX = 10;

  private static int digitAt(String elem, int digitPos) {
    return elem.charAt(digitPos) - '0';
  }

  public static void radixSort(String[] arr/* should contain 3-digits numbers, e.g. 123, 905, etc. */) {
    rangeCountingSort(arr, 0, arr.length, 0);
  }

  private static void rangeCountingSort(String[] arr, int from, int to, int digitPos) {
    final int length = to - from;
    if (length < 2 || digitPos >= DIGITS) {
      return; // optimization for empty or 1-element array - or - digit count exceeded
    }

    final int[] frequences = new int[DIGIT_MAX]; // possible optimization: can be united with offsets

    // get statistics for digits at start position
    //noinspection ForLoopReplaceableByForEach
    for (int i = from; i < to; ++i) {
      final int digit = digitAt(arr[i], digitPos);
      assert digit >= 0 && digit <= 9;
      ++frequences[digit];
    }

    // initialize remaining digits with arr.length to simplify conversion code
    final int[] offsets = new int[DIGIT_MAX + 1];
    offsets[DIGIT_MAX] = length;
    for (int i = 0, offset = from; i < frequences.length; ++i) {
      offsets[i] = offset;
      offset = offset + frequences[i];
    }

    //System.out.println("(" + digitPos + ", f=" + from + ", t=" + to + ") [1] Frequences=" + Arrays.toString(frequences) + ", offsets=" + Arrays.toString(offsets));

    // sort array in range
    final int[] bounds = Arrays.copyOf(offsets, offsets.length);
    for (int i = from; i < to; ++i) {
      String elem = arr[i];

      for (;;) {
        int digit = digitAt(elem, digitPos);
        // move element to where it should belong to
        int offset = offsets[digit];
        if (i >= offset && i < offsets[digit + 1]) {
          // no need to shuffle, keep element on its place
          //System.out.println("(" + digitPos + ", f=" + from + ", t=" + to + ") [2a] Element " + elem + " is on its place, continue...");
          break;
        }

        // start moving element
        int j = bounds[digit]; // new index
        ++bounds[digit]; // increment bounds index

        //System.out.println("(" + digitPos + ", f=" + from + ", t=" + to + ") [2b] Element " + elem + " needs to be moved to " + j + " position");

        // swap elements
        final String savedElem = arr[j];
        arr[j] = elem;
        elem = savedElem;
        arr[i] = elem;
      }
    }

    //System.out.println("(" + digitPos + ", f=" + from + ", t=" + to + ") [3] Partially sorted array=" + Arrays.toString(arr));

    // Then - recursively sort subarrays
    for (int i = 0; i < DIGIT_MAX; ++i) {
      rangeCountingSort(arr, offsets[i], offsets[i + 1], digitPos + 1);
    }
  }
}
