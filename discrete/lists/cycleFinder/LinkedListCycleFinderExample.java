import support.SingleLinkedListSupport;

/**
 * Sample run:
 * <pre>
 * Loop element in a list [1] is <none>
 * Loop element in a list [1 -> 2 -> 3] is <none>
 * Loop element in a list [1 -> 1] is 1
 * Loop element in a list [1 -> 2 -> @1] is 1
 * Loop element in a list [1 -> 2 -> @2] is 2
 * Loop element in a list [1 -> 2 -> 3 -> 4 -> 5 -> @3] is 3
 * </pre>
 *
 * @author Alexander Shabanov
 */
public class LinkedListCycleFinderExample extends SingleLinkedListSupport {

  public static void main(String[] args) {
    demo("[1]", fromArray(new Integer[] { 1 }));
    demo("[1 -> 2 -> 3]", fromArray(new Integer[] { 1, 2, 3 }));

    {
      final Node<Integer> node = newNode(1, null);
      node.setNext(node);
      demo("[1 -> 1]", node);
    }

    {
      final Node<Integer> n1 = newNode(2, null);
      final Node<Integer> node = newNode(1, n1);
      n1.setNext(node);
      demo("[1 -> 2 -> @1]", node);
    }

    {
      final Node<Integer> n1 = newNode(2, null);
      final Node<Integer> node = newNode(1, n1);
      n1.setNext(n1);
      demo("[1 -> 2 -> @2]", node);
    }

    {
      final Node<Integer> node = fromArray(new Integer[] { 1, 2, 3, 4, 5 });
      final Node<Integer> n3 = node.getNext().getNext();
      final Node<Integer> n5 = n3.getNext().getNext();
      n5.setNext(n3);
      demo("[1 -> 2 -> 3 -> 4 -> 5 -> @3]", node);
    }
  }

  private static <T> void demo(String listName, Node<T> nodes) {
    final Node<T> loopStart = findLoopStart(nodes);
    System.out.println("Loop element in a list " + listName + " is " +
        (loopStart != null ? loopStart.getValue() : "<none>"));
  }

  //
  // Private
  //

  private static <T> Node<T> findLoopStart(Node<T> list) {
    // find whether a list has loop in the first place
    // and keep track of its position
    if (list == null) {
      return null;
    }

    Node<T> c = list; // regular cursor
    int pos = 0;
    Node<T> lc = list.getNext(); // lc is a lookahead cursor, that moves twice as fast as regular cursor

    for (;; c = c.getNext(), lc = lc.getNext(), ++pos) {
      if (c == null || lc == null) {
        return null;
      }

      if (c == lc) {
        break;
      }

      lc = lc.getNext();
      if (lc == null) {
        return null;
      }

      if (c == lc) {
        break;
      }
    }

    // if we're here, it means loop has been detected, now we need to figure out its length
    int loopSize = 1;
    for (lc = c.getNext();; lc = lc.getNext(), ++loopSize) {
      if (c == lc) {
        break;
      }
    }

    // ok, now we have size and cursor position, now estimate for loop start
    final int startPosMin = Math.max(0, pos - loopSize);

    // skip start pos min elements
    c = list;
    for (int i = 0; i < startPosMin; ++i) {
      c = c.getNext();
    }

    // now just verify every node by traversing exactly loopSize times
    int loopIterationCap = pos + loopSize + 1 /* worst case scenario */;
    int tries = 0;
    for (c = list; tries < loopIterationCap; c = c.getNext(), ++tries) {
      lc = c.getNext();
      for (int i = 0; i < loopSize; ++i, lc = lc.getNext()) {
        if (c == lc) {
          return c;
        }
      }
    }

    // if we're here, loop is either modified or code above has a bug
    throw new IllegalStateException("Invariant failed: loop not found in a given list");
  }
}
