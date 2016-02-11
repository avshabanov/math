import support.SingleLinkedListSupport;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * Sample run:
 * <pre>
 * Source=[], reverse=null
 * Source=[a], reverse=[a]
 * Source=[a, b, c], reverse=[c, b, a]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class ListReverseExample extends SingleLinkedListSupport {

  public static void main(String[] args) {
    demo(new String[0]);
    demo(new String[] {"a"});
    demo(new String[] {"a", "b", "c"});
  }

  public static void demo(String[] arr) {
    final Node<String> n = fromArray(arr);
    final Node<String> r = reverse(n);

    final List<String> rev = new ArrayList<>(Arrays.asList(arr));
    Collections.reverse(rev);

    if (!rev.equals(new ArrayList<>(Arrays.asList(toArray(r, new String[0]))))) {
      throw new AssertionError("Reversal don't match, source=" + n + ", rev=" + r);
    }

    System.out.println("Source=" + Arrays.toString(arr) + ", reverse=" + r);
  }

  public static <T> Node<T> reverse(final Node<T> list) {
    Node<T> last = list;
    Node<T> prev = null;
    for (; last != null;) {
      final Node<T> next = last.getNext();
      last.setNext(prev);
      prev = last;
      if (next == null) {
        break;
      }
      last = next;
    }
    return last;
  }
}
