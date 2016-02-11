import java.util.Arrays;

/**
 * Sample run:
 * <pre>
 * Intersection of [] and [] is []
 * Intersection of [] and [1] is []
 * Intersection of [1] and [] is []
 * Intersection of [1] and [2] is []
 * Intersection of [1] and [1] is [1]
 * Intersection of [1] and [1, 2] is [1]
 * Intersection of [1, 3] and [1, 2] is [1]
 * Intersection of [3, 2, 1, 1, 1] and [1, 2, 2, 3, 3] is [1, 2, 3]
 * Intersection of [9, 7, 7, 1, 2, 4, 5, 6, 9] and [4, 4, 1, 3, 9, 8, 5, 4] is [1, 4, 5, 9]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class IntersectionExample {

  public static void main(String[] args) {
    demo(new int[0], new int[0]);
    demo(new int[0], new int[] { 1 });
    demo(new int[] { 1 }, new int[0]);
    demo(new int[] { 1 }, new int[] { 2 });
    demo(new int[] { 1 }, new int[] { 1 });
    demo(new int[] { 1 }, new int[] { 1, 2 });
    demo(new int[] { 1, 3 }, new int[] { 1, 2 });
    demo(new int[] { 3, 2, 1, 1, 1 }, new int[] { 1, 2, 2, 3, 3 });
    demo(new int[] { 9, 7, 7, 1, 2, 4, 5, 6, 9 }, new int[] { 4, 4, 1, 3, 9, 8, 5, 4 });
  }

  public static void demo(int[] a1, int[] a2) {
    System.out.println("Intersection of " + Arrays.toString(a1) + " and " + Arrays.toString(a2) + " is " +
        Arrays.toString(getIntersection(a1, a2)));
  }

  public static int[] getIntersection(int[] arr1, int[] arr2) {
    // copy and sort
    final int[] a1 = Arrays.copyOf(arr1, arr1.length);
    final int[] a2 = Arrays.copyOf(arr2, arr2.length);

    Arrays.sort(a1);
    Arrays.sort(a2);

    // prepare the result
    final int[] result = new int[Math.max(arr1.length, arr2.length)];
    int rs = 0; // rs = result size

    for (int i1 = 0, i2 = 0; i1 < a1.length; ++i1) {
      final int element = a1[i1];
      int j = i2;

      // find matching element in the second array
      boolean found = false;
      while (j < a2.length) {
        if (a2[j] == element) {
          found = true;
          break;
        }
        if (a2[j] < element) {
          ++j;
        } else {
          break;
        }
      }
      i2 = j;
      if (i2 == a2.length) {
        break; // done with the second array
      }

      if (!found) {
        continue;
      }

      if (rs > 0 && result[rs - 1] == element) {
        continue; // this is a duplicate, continue to the next one
      }

      // insert this element
      result[rs] = element;
      ++rs;
    }

    return Arrays.copyOf(result, rs);
  }
}
