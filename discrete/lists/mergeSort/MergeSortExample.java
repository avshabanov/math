import support.SingleLinkedListSupport;

/**
 * Sample run:
 * <pre>
 * Merging lists: [3, 2, 1] result=[1, 2, 3]
 * Merging lists: [8, 4, 6, 2] [3, 7, 1, 5] result=[1, 2, 3, 4, 5, 6, 7, 8]
 * Merging lists: [4, 64, 1] [16] [32, 2] result=[1, 2, 4, 16, 32, 64]
 * </pre>
 */
public final class MergeSortExample extends SingleLinkedListSupport {
  public static void main(String[] args) {
    demo(fromArray(new Integer[] { 3, 2, 1 }));
    demo(fromArray(new Integer[] { 8, 4, 6, 2 }), fromArray(new Integer[] { 3, 7, 1, 5 }));
    demo(fromArray(new Integer[] { 4, 64, 1 }), fromArray(new Integer[] { 16 }), fromArray(new Integer[] { 32, 2 }));
  }

  @SafeVarargs
  public static <T extends Comparable<T>> void demo(Node<T>... lists) {
    final StringBuilder sb = new StringBuilder();
    sb.append("Merging lists: ");
    for (final Node<T> l : lists) {
      sb.append(l.toString()).append(' ');
    }
    sb.append("result=").append(merge(lists));

    System.out.println(sb.toString());
  }

  // Option 1: direct approach

  @SafeVarargs
  public static <T extends Comparable<T>> Node<T> merge(Node<T>... lists) {
    Node<T> result = null;
    for (final Node<T> l : lists) {
      result = mergeWithSorted(result, l);
    }
    return result;
  }

  private static <T extends Comparable<T>> Node<T> mergeWithSorted(Node<T> sorted, Node<T> unsorted) {
    Node<T> result = sorted;

    for (Node<T> it = unsorted; it != null; it = it.getNext()) {
      final T value = it.getValue(); // TODO: null checks

      // find position to insert
      Node<T> after = null;
      for (Node<T> r = result; r != null; r = r.getNext()) {
        if (value.compareTo(r.getValue()) < 0) {
          break;
        }
        after = r;
      }

      if (after == null) {
        result = newNode(value, result);
      } else {
        after.setNext(newNode(value, after.getNext()));
      }
    }

    return result;
  }
}
