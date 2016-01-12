import java.util.Arrays;

/**
 * Demo output:
 * <pre>
 * Given array=[10] element with the biggest number of repetitions is 10
 * Given array=[10, 20, 30] element with the biggest number of repetitions is 10
 * Given array=[10, 10, 20, 30] element with the biggest number of repetitions is 10
 * Given array=[10, 20, 20, 30] element with the biggest number of repetitions is 20
 * Given array=[10, 20, 30, 30] element with the biggest number of repetitions is 30
 * Given array=[10, 20, 20] element with the biggest number of repetitions is 20
 * Given array=[30, 30, 30, 40, 40, 40, 40] element with the biggest number of repetitions is 40
 * Given array=[10, 20, 20, 10, 30, 10] element with the biggest number of repetitions is 10
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class FindMaxRepetitionExample {

  public static void main(String[] args) {
    demo(new int[] { 10 });
    demo(new int[] { 10, 20, 30 });
    demo(new int[] { 10, 10, 20, 30 });
    demo(new int[] { 10, 20, 20, 30 });
    demo(new int[] { 10, 20, 30, 30 });
    demo(new int[] { 10, 20, 20 });
    demo(new int[] { 30, 30, 30, 40, 40, 40, 40 });
    demo(new int[] { 10, 20, 20, 10, 30, 10 });
  }

  static void demo(int[] arr) {
    System.out.println("Given array=" + Arrays.toString(arr) + " element with the biggest number of repetitions is " +
      getElementWithTheBiggestNumberOfRepetitions(arr));
  }

  //
  // Private
  //

  private static int getElementWithTheBiggestNumberOfRepetitions(int[] arr) {
    if (arr == null || arr.length == 0) {
      throw new IllegalArgumentException("array is null or empty");
    }

    // [1] copy and sort
    int[] a = Arrays.copyOf(arr, arr.length);
    Arrays.sort(a);
    int resultElement = 0;
    int maxRepetitions = 0;

    int previousElement = 0;
    int repetitions = 1;
    for (int i = 0; i < a.length; ++i) {
      if (i == 0) {
        previousElement = a[0];
        continue;
      }

      // does new element matches previous one?
      final int newElement = a[i];
      if (newElement == previousElement) {
        ++repetitions;
        continue;
      }

      // new element, match this candidate with the previously recorded one
      if (repetitions > maxRepetitions) {
        resultElement = previousElement;
        maxRepetitions = repetitions;
      }

      // reset repetitions counter
      repetitions = 1;
      previousElement = newElement;
    }

    // compare repetitions for the last element
    return repetitions > maxRepetitions ? a[a.length - 1] : resultElement;
  }
}
