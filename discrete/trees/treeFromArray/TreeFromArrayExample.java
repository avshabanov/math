import support.SimpleTreeSupport;

import java.util.Arrays;

/**
 * Sample run:
 * <pre>
 * Tree from array=[2]:
 * 2
 *
 * Tree from array=[1, 2]:
 *   1
 * 2
 *
 * Tree from array=[1, 2, 3]:
 *   1
 * 2
 *   3
 *
 * Tree from array=[1, 2, 3, 4, 5, 6, 7]:
 *     1
 *   2
 *     3
 * 4
 *     5
 *   6
 *     7
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class TreeFromArrayExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(2);
    demo(1, 2);
    demo(1, 2, 3);
    demo(1, 2, 3, 4, 5, 6, 7);
  }

  public static void demo(int... arr) {
    Arrays.sort(arr);
    System.out.println("Tree from array=" + Arrays.toString(arr) + ":\n" + asString(fromArray(arr)));
  }

  public static Node fromArray(int[] array) {
    return fromArrayHelper(array, 0, array.length);
  }

  private static Node fromArrayHelper(int[] array, int left, int right) {
    if (left == right) {
      return null; // no elements
    }

    final int med = (left + right) / 2;
    return new Node(array[med], fromArrayHelper(array, left, med), fromArrayHelper(array, med + 1, right));
  }
}
