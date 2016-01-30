import support.SimpleTreeSupport;

/**
 * @author Alexander Shabanov
 */
public final class BstVerificationExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    // valid BSTs
    final Node bst1 = n(1);
    final Node bst2 = n(2, n(1), n(3));

    // invalid BSTs
    final Node t1 = n(2, n(3), null);
    final Node t2 = n(2, null, n(1));

    demo(bst1, true);
    demo(bst2, true);

    demo(t1, false);
    demo(t2, false);
  }

  public static void demo(Node tree, boolean shouldBeValid) {
    if (shouldBeValid != isValidRecursive(tree)) {
      throw new AssertionError("[RecurCheck] " + !shouldBeValid + " returned, but " + shouldBeValid + " expected.");
    }
    System.out.println("[RecurCheck] OK: A tree is " + (shouldBeValid ? "valid" : "not valid") + " BST.");
  }

  private static boolean isValidRecursive(Node node) {
    final int value = node.getValue();

    final Node left = node.getLeft();
    if (left != null) {
      if (value <= left.getValue() || !isValidRecursive(left)) {
        return false;
      }
    }

    final Node right = node.getRight();
    if (right != null) {
      if (value >= right.getValue() || !isValidRecursive(right)) {
        return false;
      }
    }

    return true;
  }
}
