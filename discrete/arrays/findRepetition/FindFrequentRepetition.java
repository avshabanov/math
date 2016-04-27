import java.util.Arrays;

/**
 * TBD.
 */
public final class FindFrequentRepetition {

  public static void main(String[] args) {
    demo(new int[] { 1 });
    demo(new int[] { 1, 2, 1 });
    demo(new int[] { 1, 2, 1, 2, 1 });
    demo(new int[] { 1, 2, 1, 2, 2, 1, 2 });
    demo(new int[] { 1, 1, 2, 2, 2, 2, 2, 1, 1 });
    demo(new int[] { 1, 1, 2, 2, 2, 1, 1 });
    demo(new int[] { 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1 });
    demo(new int[] { 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2 });
    demo(new int[] { 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2 });
  }

  public static void demo(int[] arr) {
    System.out.println("Max repetition in arr=" + Arrays.toString(arr) +
        " is " + findN2Repetition(arr));
  }

  /**
   * Looks up and returns elements that repeats more than ceil(N/2) times, where N is the size of the array.
   * This function assumes that this element always exists for any given array.
   *
   * @param arr Array, to look repetition in
   * @return Element, that repeats more than ceil(arr.length / 2) times
   */
  public static int findN2Repetition(int[] arr) {
    if (arr.length == 0) {
      throw new IllegalArgumentException("Given array is empty");
    }

    int candidate = arr[0];
    int counter = 1;

    for (int i = 1; i < arr.length; ++i) {
      final int elem = arr[i];
      if (elem == candidate) {
        ++counter;
        continue;
      }

      --counter;
      if (counter == 0) {
        candidate = elem;
        counter = 1;
      }
    }

    // return corresponding element
    return candidate;
  }
}
