import support.SimpleTreeSupport;

import java.util.Objects;

/**
 * Sample run:
 * <pre>
 * A value closest to 0 is null for tree:
 * (null)
 * A value closest to 10 is 1 for tree:
 * 1
 *
 * A value closest to 100 is 50 for tree:
 *     12
 *       14
 *   15
 *       17
 *     18
 * 20
 *       25
 *     30
 *       35
 *   40
 *     50
 *
 * A value closest to 0 is 12 for tree: (same as above)
 * A value closest to 21 is 20 for tree: (same as above)
 * A value closest to 18 is 18 for tree: (same as above)
 * A value closest to 49 is 50 for tree: (same as above)
 * A value closest to 51 is 50 for tree: (same as above)
 * A value closest to 29 is 30 for tree: (same as above)
 * A value closest to 31 is 30 for tree: (same as above)
 * A value closest to 24 is 25 for tree: (same as above)
 * A value closest to 26 is 25 for tree: (same as above)
 * A value closest to 34 is 35 for tree: (same as above)
 * A value closest to 36 is 35 for tree: (same as above)
 * A value closest to 39 is 40 for tree: (same as above)
 * A value closest to 41 is 40 for tree: (same as above)
 * A value closest to 40 is 40 for tree: (same as above)
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class CloseValuesExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(null, 0, null);
    demo(n(1), 10, 1);

    final Node tree = treeFromArray(20, 15, 40, 12, 18, 30, 50, 14, 17, 25, 35);
    demo(tree, 100, 50);
    demo(tree, 0, 12, true);
    demo(tree, 21, 20, true);
    demo(tree, 18, 18, true);
    demo(tree, 49, 50, true);
    demo(tree, 51, 50, true);
    demo(tree, 29, 30, true);
    demo(tree, 31, 30, true);
    demo(tree, 24, 25, true);
    demo(tree, 26, 25, true);
    demo(tree, 34, 35, true);
    demo(tree, 36, 35, true);
    demo(tree, 39, 40, true);
    demo(tree, 41, 40, true);
    demo(tree, 40, 40, true);
  }

  public static void demo(Node tree, int value, Integer expected) {
    demo(tree, value, expected, false);
  }

  public static void demo(Node tree, int value, Integer expected, boolean sameAsAbove) {
    System.out.println("A value closest to " + value + " is " + expected + " for tree:" +
        (sameAsAbove ? " (same as above)" : "\n" + asString(tree)));
    check(SimpleRecursive.getClosestValue(tree, value), expected, "SimpleRecursive");
    check(OptRecursive.getClosestValue(tree, value), expected, "OptRecursive");
  }

  private static void check(Node resultantNode, Integer expected, String producedValueDescription) {
    if (expected == null) {
      if (resultantNode != null) {
        throw new AssertionError(producedValueDescription + " returned a value, but not expected to");
      }

      return;
    }

    if (resultantNode == null || !Objects.equals(resultantNode.getValue(), expected)) {
      throw new AssertionError(producedValueDescription +  " didn't return a value=" + expected +
          ", returned=" + resultantNode);
    }
  }

  /**
   * Least optimal solution - scans all nodes, can be optimized to take into an account BST properties
   * however this solution would work for arbitrary trees (not necessarily search trees).
   */
  public static final class SimpleRecursive {

    public static Node getClosestValue(Node node, int value) {
      if (node == null) {
        return null;
      }

      final long nodeDiff = Math.abs(((long) value) - node.getValue());

      final Node left = getClosestValue(node.getLeft(), value);
      final long leftDiff = left == null ? nodeDiff : Math.abs(((long) left.getValue()) - value);

      final Node right = getClosestValue(node.getRight(), value);
      final long rightDiff = right == null ? nodeDiff : Math.abs(((long) right.getValue()) - value);

      final Node smallestChild;
      final long smallestChildDiff;
      if (leftDiff < rightDiff) {
        smallestChild = left;
        smallestChildDiff = leftDiff;
      } else {
        smallestChild = right;
        smallestChildDiff = rightDiff;
      }

      if (nodeDiff > smallestChildDiff) {
        return smallestChild;
      }

      return node;
    }
  }

  /**
   * More effective solution than brute-force recursion in {@link CloseValuesExample.SimpleRecursive},
   * but works only with BSTs.
   */
  public static final class OptRecursive {

    public static Node getClosestValue(Node node, int value) {
      if (node == null) {
        return null;
      }

      if (value == node.getValue()) {
        return node;
      }

      final long diff = ((long) value) - node.getValue();
      if (value < node.getValue()) {
        // try left subtree - values in the right subtree will definitely produce bigger diff
        final Node left = getClosestValue(node.getLeft(), value);
        if (left == null) {
          return node;
        }

        final long leftDiff = Math.abs(((long) value) - left.getValue());
        return leftDiff < (-diff) ? left : node;
      }

      // try right subtree
      // try left subtree - values in the right subtree will definitely produce bigger diff
      final Node right = getClosestValue(node.getRight(), value);
      if (right == null) {
        return node;
      }

      final long rightDiff = Math.abs(((long) value) - right.getValue());
      return rightDiff < diff ? right : node;
    }
  }
}
