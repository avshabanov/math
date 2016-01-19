import java.util.Arrays;
import java.util.Comparator;

/**
 * Sample run:
 * <pre>
 * Looking for element=b in array=[a, b, c] : index=1
 * Looking for element=0 in array=[a, b, c] : index=0
 * Looking for element=z in array=[a, b, c] : index=3
 * Looking for element=c in array=[a, b, d] : index=2
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class BinarySearchExample {

  public static void main(String[] args) {
    demo(new String[]{"a", "b", "c"}, "b", String::compareTo);
    demo(new Character[]{'a', 'b', 'c'}, '0', Character::compareTo);
    demo(new Character[]{'a', 'b', 'c'}, 'z', Character::compareTo);
    demo(new Character[]{'a', 'b', 'd'}, 'c', Character::compareTo);
  }

  static <T> void demo(T[] array, T element, Comparator<T> comparator) {
    Arrays.sort(array, comparator);
    System.out.println("Looking for element=" + element + " in array=" + Arrays.toString(array) +
        " : index=" + findElementIndex(array, element, comparator));
  }

  //
  // Private
  //

  static <T> int findElementIndex(T[] arr, T element, Comparator<T> comparator) {
    int left = 0;
    int right = arr.length;
    while (right > left) {
      final int med = (left + right) / 2;
      final int res = comparator.compare(element, arr[med]);
      if (res == 0) {
        return med;
      } else if (res < 0) {
        right = med;
      } else {
        left = med + 1;
      }
    }

    return left;
  }
}
