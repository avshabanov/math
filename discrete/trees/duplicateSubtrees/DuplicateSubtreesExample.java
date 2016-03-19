import support.SimpleTreeSupport;

/**
 * Sample output:
 * <pre>
 * There are no duplicate subtrees in a tree
 * There are no duplicate subtrees in a tree
 * There are no duplicate subtrees in a tree
 * There are duplicate subtrees in a tree
 * There are duplicate subtrees in a tree
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class DuplicateSubtreesExample extends SimpleTreeSupport {

  private static final int MIN_HEIGHT_OF_SUBTREE = 2; // this is to ignore subtrees of one parent and two leaf nodes

  public static void main(String[] args) {
    demo(n(1));
    demo(n(3, n(1), n(1)));
    demo(n(3,
        n(7, n(9), n(9)),
        n(7, n(9), n(9))));
    demo(n(8,
        n(5, n(3, n(1), n(1)), n(7, n(9), n(9))),
        n(5, n(3, n(1), n(1)), n(7, n(9), n(9)))));
    demo(n(8,
        n(5, n(3, n(1), n(1)), n(7, n(9), n(9))),
        n(6, n(9), n(5, n(3, n(1), n(1)), n(7, n(9), n(9))))));
  }

  public static void demo(Node tree) {
    System.out.println("There are" + (hasDuplicateSubtrees(tree) ? "" : " no") +
        " duplicate subtrees in a tree" +
        //":\n" + asString(tree) + "--\n" +
        "");
  }

  private static boolean hasDuplicateSubtrees(Node node) {
    if (node == null) {
      return false;
    }
    return compareSubtrees(node.getLeft(), node.getRight());
  }

  private static boolean compareSubtrees(Node lhs, Node rhs) {
    if (sameTrees(lhs, rhs, 0)) {
      return true;
    }

    if (lhs == null || rhs == null) {
      return false;
    }

    return sameTrees(lhs, rhs.getLeft(), 0) || sameTrees(lhs, rhs.getRight(), 0) ||
        sameTrees(lhs.getLeft(), rhs, 0) || sameTrees(lhs.getRight(), rhs, 0);
  }

  private static boolean sameTrees(Node lhs, Node rhs, int depth) {
    if (lhs == null) {
      return rhs == null && depth > MIN_HEIGHT_OF_SUBTREE;
    }

    if (rhs == null) {
      return false;
    }

    if (lhs.getValue() != rhs.getValue()) {
      return false;
    }

    return sameTrees(lhs.getLeft(), rhs.getLeft(), depth + 1) && sameTrees(lhs.getRight(), rhs.getRight(), depth + 1);
  }
}
