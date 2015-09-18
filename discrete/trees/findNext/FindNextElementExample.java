import support.SimpleTreeSupport;

/**
 * Illustrates an implementation of an algorithm that finds next element which is strictly greater than the given one.
 *
 * @author Alexander Shabanov
 */
public final class FindNextElementExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo("tree1", n(50, n(30, n(10), n(40)), n(70, n(60), n(80))), 30, 55, 75);
  }

  //
  // Private
  //

  private static void demo(String treeName, Node node, int... values) {
    System.out.println(treeName + "=\n" + asString(node));
    for (final int val : values) {
      System.out.println("\tnext for " + val + " = " + findNext(node, val));
    }
  }

  private static int findNext(Node root, int element) {
    if (root == null) {
      throw new RuntimeException();
    }

    if (element >= root.getValue()) {
      // go to the right subtree
      return findNext(root.getRight(), element);
    }

    // element is strictly less than the given one - now we need to pick up the leftmost element
    Node node = root;
    while (node.getLeft() != null) {
      final Node left = node.getLeft();
      if (element >= left.getValue()) {
        // go to the right subtree - or - pick the parent
        if (left.getRight() != null) {
          return findNext(left.getRight(), element);
        } else {
          return node.getValue();
        }
      }
      node = left;
    }
    return node.getValue();
  }
}
