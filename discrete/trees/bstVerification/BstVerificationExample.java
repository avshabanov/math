import support.SimpleTreeSupport;

import java.util.ArrayDeque;
import java.util.Deque;

/**
 * @author Alexander Shabanov
 */
public final class BstVerificationExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    // valid BSTs
    final Node bst1 = n(1);
    final Node bst2 = n(2, n(1), n(3));
    final Node bst3 = n(
        50,
        n(30,
            n(20,
                n(15), n(25)),
            n(40,
                n(35), n(45))),
        n(70,
            n(60,
                n(55), n(65)),
            n(80,
                n(75), n(85))));

    // invalid BSTs
    final Node t1 = n(2, n(3), null);
    final Node t2 = n(2, null, n(1));
    final Node t3 = n(
        50,
        n(30,
            n(20,
                n(15), n(25)),
            n(40,
                n(35), n(45))),
        n(70,
            n(60,
                n(55), n(65)),
            n(80,
                n(75), n(77))));
    final Node t4 = n(
        50,
        n(30,
            n(20,
                n(21), n(25)),
            n(40,
                n(35), n(45))),
        n(70,
            n(60,
                n(55), n(65)),
            n(80,
                n(75), n(85))));
    final Node t5 = n(
        50,
        n(30,
            n(20,
                n(15), n(25)),
            n(40,
                n(35), n(39))),
        n(70,
            n(60,
                n(55), n(65)),
            n(80,
                n(75), n(85))));
    final Node t6 = n(
        50,
        n(30,
            n(20,
                n(15), n(25)),
            n(40,
                n(35), n(45))),
        n(70,
            n(60,
                n(55), n(89)),
            n(80,
                n(75), n(85))));
    final Node t7 = n(
        50,
        n(30,
            n(20,
                n(15), n(25)),
            n(40,
                n(35), n(45))),
        n(70,
            n(60,
                n(61), n(65)),
            n(80,
                n(75), n(85))));
    final Node t8 = n(
        50,
        n(30,
            n(20,
                n(15), n(25)),
            n(40,
                n(35), n(45))),
        n(70,
            n(60,
                n(10), n(65)),
            n(80,
                n(75), n(85))));
    final Node t9 = n(
        50,
        n(30,
            n(20,
                n(15), n(25)),
            n(40,
                n(35), n(89))),
        n(70,
            n(60,
                n(55), n(65)),
            n(80,
                n(75), n(85))));

    demo(bst1, true);
    demo(bst2, true);
    demo(bst3, true);

    demo(t1, false);
    demo(t2, false);
    demo(t3, false);
    demo(t4, false);
    demo(t5, false);
    demo(t6, false);
    demo(t7, false);
    demo(t8, false);
    demo(t9, false);
  }

  public static void demo(Node tree, boolean shouldBeValid) {
    if (shouldBeValid != isValidRecursive(tree)) {
      System.out.println("[RecurCheck] For tree:\n" + asString(tree));
      throw new AssertionError("[RecurCheck] " + !shouldBeValid + " returned, but " + shouldBeValid + " expected.");
    }
    if (shouldBeValid != isValidNonRecursive(tree)) {
      System.out.println("[NonRecurCheck] For tree:\n" + asString(tree));
      throw new AssertionError("[NonRecurCheck] " + !shouldBeValid + " returned, but " + shouldBeValid + " expected.");
    }
    System.out.println("OK: A tree is " + (shouldBeValid ? "valid" : "not valid") + " BST.");
  }

  // Recursive validation

  private static boolean isValidRecursive(Node node) {
    return isValidRecursiveHelper(node, null, null);
  }

  private static boolean isValidRecursiveHelper(Node child, Node leftBound, Node rightBound) {
    if (child == null) {
      return true;
    }

    final int value = child.getValue();
    if (leftBound != null && value <= leftBound.getValue()) {
      return false;
    }

    if (rightBound != null && value >= rightBound.getValue()) {
      return false;
    }

    return isValidRecursiveHelper(child.getLeft(), leftBound, child) && isValidRecursiveHelper(child.getRight(),
        child, rightBound);
  }

  // Non-recursive validation

  private static boolean isValidNonRecursive(Node node) {
    final Deque<NonRecHelperEntry> entries = new ArrayDeque<>();
    if (node != null) {
      entries.add(new NonRecHelperEntry(node, null, null));
    }

    while (!entries.isEmpty()) {
      final NonRecHelperEntry e = entries.removeLast();
      final Node child = e.node;
      final int value = child.getValue();

      if (e.leftBound != null && value <= e.leftBound.getValue()) {
        return false;
      }

      if (e.rightBound != null && value >= e.rightBound.getValue()) {
        return false;
      }

      if (child.getRight() != null) {
        entries.add(new NonRecHelperEntry(child.getRight(), child, e.rightBound));
      }

      if (child.getLeft() != null) {
        entries.add(new NonRecHelperEntry(child.getLeft(), e.leftBound, child));
      }
    }

    return true;
  }

  private static final class NonRecHelperEntry {
    final Node node;
    final Node leftBound;
    final Node rightBound;

    public NonRecHelperEntry(Node node, Node leftBound, Node rightBound) {
      this.node = node;
      this.leftBound = leftBound;
      this.rightBound = rightBound;
    }
  }
}
