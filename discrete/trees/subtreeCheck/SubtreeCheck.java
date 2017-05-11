import support.SimpleTreeSupport;

/**
 * Problem: https://leetcode.com/problems/subtree-of-another-tree/#/description
 *
 * <p>
 * Given two non-empty binary trees s and t, check whether tree t has exactly the same structure and node values with a
 * subtree of s. A subtree of s is a tree consists of a node in s and all of this node's descendants.
 * The tree s could also be considered as a subtree of itself.
 * </p>
 */
public final class SubtreeCheck extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(null, null);
    demo(n(1), n(1));
    demo(n(1), n(2));
    demo(n(1), n(1, null, n(2)));
    demo(
        n(3, n(4, n(1), n(2)), n(5)),
        n(4, n(1), n(2)));
    demo(
        n(3, n(4, n(1), null), n(5)),
        n(4, n(1), n(2)));
    demo(n(2, n(1), n(3)), n(2, n(1), n(3)));
  }

  private static void demo(Node tree, Node subtree) {
    System.out.printf("Tree:\n%s\nSubtree:\n%s\nHasSubtree = %s\n===\n",
        asString(tree),
        asString(subtree),
        hasSubtree(tree, subtree));
  }

  private static boolean hasSubtree(Node tree, Node subtree) {
    if (tree == null) {
      return subtree == null;
    }

    if (subtree == null) {
      return false;
    }

    final int source = tree.getValue();
    final int target = subtree.getValue();

    return source == target && hasSubtree(tree.getLeft(), subtree.getLeft()) &&
        hasSubtree(tree.getRight(), subtree.getRight()) ||
        hasSubtree(tree.getLeft(), subtree) ||
        hasSubtree(tree.getRight(), subtree);

    // If this tree is a binary search tree:
//    if (source == target) {
//      return hasSubtree(tree.getLeft(), subtree.getLeft()) && hasSubtree(tree.getRight(), subtree.getRight());
//    }
//    if (source < target) {
//      // check right subtree
//      return hasSubtree(tree.getRight(), subtree);
//    }
//
//    // source > tree => check left subtree
//    return hasSubtree(tree.getLeft(), subtree);
  }
}
