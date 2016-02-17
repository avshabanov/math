import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.TreeSet;
import java.util.stream.Collectors;

/**
 * Inplace insertion sort that also removes duplicates.
 * <pre>
 * Sorted=[], arr=[]
 * Sorted=[1], arr=[1]
 * Sorted=[1, 2], arr=[1, 2]
 * Sorted=[1], arr=[1, 1, 1]
 * Sorted=[1, 4], arr=[4, 1, 4, 1]
 * Sorted=[1, 2, 3, 4, 5], arr=[1, 2, 3, 4, 5]
 * Sorted=[1, 2, 3], arr=[1, 2, 2, 3, 3, 3]
 * Sorted=[1, 2, 3, 4, 5], arr=[5, 5, 4, 3, 2, 2, 3, 1]
 * Sorted=[0, 1, 2], arr=[0, 1, 2, 2, 1, 0, 1, 2, 0]
 * Sorted=[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], arr=[9, 5, 9, 4, 8, 7, 5...
 * Sorted=[12, 42, 43, 52, 54, 60, 61, 73, 74, 92], arr=[73, 61, 7...
 * Sorted=[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], arr=[7, 3, 4, 5, 2, 8, 4...
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class SortAndDuplicateRemovalExample {

  public static void main(String[] args) {
    final Random random = new Random(15234123412L);

    demo();
    demo(1);
    demo(1, 2);
    demo(1, 1, 1);
    demo(4, 1, 4, 1);
    demo(1, 2, 3, 4, 5);
    demo(1, 2, 2, 3, 3, 3);
    demo(1, 2, 2, 1, 2, 1, 1);
    demo(5, 5, 4, 3, 2, 2, 3, 1);
    demo(0, 1, 2, 2, 1, 0, 1, 2, 0);
    demo(Arrays.stream(new int[100]).map(operand -> random.nextInt(10)).toArray());
    demo(Arrays.stream(new int[10]).map(operand -> random.nextInt(100)).toArray());
    demo(Arrays.stream(new int[20]).map(operand -> random.nextInt(10)).toArray());
  }

  public static void demo(int... arr) {
    // duplicate source array as list of integers
    final List<Integer> original = Arrays.stream(arr).boxed().collect(Collectors.toList());
    // sort inplace
    final int len = duplicateRemovalInsertionSort(arr);
    // get actual result as a list of boxed integers
    final List<Integer> actual = Arrays.stream(arr, 0, len).boxed().collect(Collectors.toList());
    // get expected result using tree set
    final List<Integer> expected = new ArrayList<>(new TreeSet<>(original));

    // check that resultant array range doesn't contain duplicates
    if (!actual.equals(expected)) {
      throw new AssertionError("For arr=" + original + " actual=" + actual + ", expected=" + expected);
    }

    // check that duplicates are still exist
    if (!Arrays.stream(arr).sorted().boxed().collect(Collectors.toList())
        .equals(original.stream().sorted().collect(Collectors.toList()))) {
      throw new AssertionError("For arr=" + original + " actual array doesn't contain all the duplicates after len");
    }

    System.out.println("Sorted=" + actual + ", arr=" + original);
  }

  /**
   * Sorts an array inplace and removes duplicates. The duplicates are put at the end of array.
   * Only the first occurrence of element will be used, and next ones will be discarded.
   *
   * @param arr Array to be sorted inplace
   * @return Length of sorted array without duplicates. All the duplicates are starting at length index.
   *         If length==arr.length it means that array have no duplicates.
   */
  public static int duplicateRemovalInsertionSort(int[] arr) {
    int length = arr.length;

    OuterLoop:
    for (int i = 0; i < length;) {
      int elem = arr[i];

      // find place to insert given element into
      int insertionIndex = i;
      for (int j = i - 1; j >= 0; --j) {
        final int anotherElem = arr[j];
        // discard matching elements, if any
        while (elem == anotherElem) {
          // update length
          --length;
          if (i == length) {
            break OuterLoop; // end of array? - break
          }

          System.arraycopy(arr, i + 1, arr, i, length - i);
          arr[length] = elem; // move duplicate element outside of the sorted array range

          continue OuterLoop;
        }

        if (elem > arr[j]) {
          break;
        }
        insertionIndex = j;
      }

      // move elements to put inserted element into
      if (insertionIndex < i) {
        // Copy array chunk, this is an alternative to:
        //        for (int j = i; j > insertionIndex; --j) {
        //          arr[j] = arr[j - 1];
        //        }
        System.arraycopy(arr, insertionIndex, arr, insertionIndex + 1, i - insertionIndex);

        arr[insertionIndex] = elem;
      }
      ++i; // move to the next position
    }

    return length;
  }
}
