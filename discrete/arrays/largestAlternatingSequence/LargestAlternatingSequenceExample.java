import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * Sample run:
 * <pre>
 * Longest alternatig sequence is [] in []
 * Longest alternatig sequence is [] in [1]
 * Longest alternatig sequence is [1, 2] in [1, 2]
 * Longest alternatig sequence is [] in [2, 1]
 * Longest alternatig sequence is [1, 2] in [1, 2, 3]
 * Longest alternatig sequence is [1, 2, 1, 2, 1] in [3, 2, 1, 2, 1, 2, 1, 1, 3, 3]
 * Longest alternatig sequence is [2, 4, 2, 4, 2, 4] in [3, 3, 3, 1, 2, 1, 2, 2, 4, 2, 4, 2, 4, 8]
 * </pre>
 * @author Alexander Shabanov
 */
public final class LargestAlternatingSequenceExample {

  public static void main(String[] args) {
    demo(Collections.emptyList());
    demo(Collections.singletonList(1));
    demo(Arrays.asList(1, 2));
    demo(Arrays.asList(2, 1));
    demo(Arrays.asList(1, 2, 3));
    demo(Arrays.asList(3, 2, 1, 2, 1, 2, 1, 1, 3, 3));
    demo(Arrays.asList(3, 3, 3, 1, 2, 1, 2, 2, 4, 2, 4, 2, 4, 8));
  }

  public static void demo(List<Integer> list) {
    System.out.println("Largest alternatig sequence is " + getLargestAlternatingSequence(list) + " in " + list);
  }

  public static List<Integer> getLargestAlternatingSequence(List<Integer> list) {
    int maxStart = 0;
    int maxEnd = 0;
    int start = 0;
    int end = 0;

    boolean expectGreater = true;
    for (int pos = 1; pos < list.size(); ++pos) {
      int newEnd = -1;
      if ((expectGreater && (list.get(pos) > list.get(pos - 1))) ||
              ((!expectGreater) && (list.get(pos) < list.get(pos - 1)))) {
        newEnd = pos;
      }

      if (newEnd < 0) {
        if ((end - start) > (maxEnd - maxStart)) {
          maxStart = start;
          maxEnd = end;
        }

        start = end = pos;
        expectGreater = true;
        continue;
      }

      end = pos + 1;
      expectGreater = !expectGreater;
    }

    // check for closing sequence
    if ((end - start) > (maxEnd - maxStart)) {
      maxStart = start;
      maxEnd = end;
    }

    return Collections.unmodifiableList(new ArrayList<>(list.subList(maxStart, maxEnd)));
  }
}
