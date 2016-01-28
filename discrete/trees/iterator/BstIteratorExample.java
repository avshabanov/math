import support.SimpleTreeSupport;

import java.util.*;

/**
 * @author Alexander Shabanov
 */
public final class BstIteratorExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(null);
    demo(n(1));
    demo(n(2, n(1), n(3)));
    demo(n(2, n(1), n(3)));
    demo(treeFromArray(20, 15, 40, 12, 18, 30, 50, 14, 17, 25, 35));
  }

  public static void demo(Node tree) {
    System.out.println("---\nTree:\n" + asString(tree));
    System.out.print("Iterable: [");
    boolean next = false;
    for (final Integer value : createIterable(tree)) {
      if (next) {
        System.out.print(", ");
      }
      next = true;
      System.out.print(value);
    }
    System.out.println("]");
  }

  public static Iterable<Integer> createIterable(Node root) {
    return () -> new BstIterable(root);
  }

  //
  // Private
  //

  private static final class BstIterable implements Iterator<Integer> {
    private final Deque<Node> parents = new ArrayDeque<>();

    public BstIterable(final Node root) {
      for (Node n = root; n != null; n = n.getLeft()) {
        parents.add(n);
      }
    }

    @Override
    public boolean hasNext() {
      return !parents.isEmpty();
    }

    @Override
    public Integer next() {
      if (parents.isEmpty()) {
        throw new NoSuchElementException();
      }

      final Node node = parents.removeLast();

      for (Node n = node.getRight(); n != null; n = n.getLeft()) {
        parents.add(n);
      }

      return node.getValue();
    }
  }
}
