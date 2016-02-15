import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * Sample run:
 * <pre>
 * Largest geom sequence=[] in array=[]
 * Largest geom sequence=[1] in array=[1]
 * Largest geom sequence=[1, 2] in array=[1, 2]
 * Largest geom sequence=[1, 3] in array=[1, 3, 5, 7]
 * Largest geom sequence=[3, 9, 27, 81] in array=[1, 2, 4, 3, 9, 27, 81, 5, 25, 125]
 * Largest geom sequence=[1, 2, 4, 8, 16] in array=[1, 10, 100, 1000, 1, 2, 4, 8, 16]
 * Largest geom sequence=[1, 10, 100, 1000] in array=[1, 10, 100, 1000, 1, 2, 4, 8]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class LargestGeomSubseqExample {

  public static void main(String[] args) {
    demo(Collections.emptyList());
    demo(Collections.singletonList(1));
    demo(Arrays.asList(1, 2));
    demo(Arrays.asList(1, 3, 5, 7));
    demo(Arrays.asList(1, 2, 4, 3, 9, 27, 81, 5, 25, 125));
    demo(Arrays.asList(1, 10, 100, 1000, 1, 2, 4, 8, 16));
    demo(Arrays.asList(1, 10, 100, 1000, 1, 2, 4, 8));
  }

  public static void demo(List<Integer> values) {
    System.out.println("Largest geom sequence=" + getLargestGeometricSubsequence(values) + " in array=" + values);
  }

  public static List<Integer> getLargestGeometricSubsequence(List<Integer> src) {
    int maxStart = 0;
    int maxEnd = 0;

    int start = 0;

    // TODO: replace with integer-based ratio!
    double multiplier = 0;
    boolean first = true;

    final int size = src.size();
    for (int pos = 0; pos <= size; ++pos) {
      if (pos == 0) {
        continue;
      }

      if (pos != size) {
        final double curMultiplier = src.get(pos).doubleValue() / src.get(pos - 1).doubleValue();
        if (first) {
          multiplier = curMultiplier;
          first = false;
          continue;
        }

        if (curMultiplier == multiplier) {
          continue;
        }
      }

      if ((pos - start) > (maxEnd - maxStart)) {
        maxStart = start;
        maxEnd = pos;
      }
      start = pos;
      first = true;
    }

    return src.subList(maxStart, maxEnd);
  }
}
