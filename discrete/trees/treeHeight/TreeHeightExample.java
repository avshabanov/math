import support.SimpleTreeSupport;


/**
 * Sample run:
 * <pre>
 * ---
 * Height=0 for tree:
 * (null)
 * ---
 * Height=1 for tree:
 * 1
 *
 * ---
 * Height=2 for tree:
 *   1
 * 2
 *   3
 *
 * ---
 * Height=4 for tree:
 *   1
 * 2
 *     4
 *   3
 *     5
 *       6
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class TreeHeightExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(null);
    demo(n(1));
    demo(n(2, n(1), n(3)));
    demo(n(2, n(1), n(3, n(4), n(5, null, n(6)))));
  }

  public static void demo(Node tree) {
    System.out.println("---\nHeight=" + getTreeHeight(tree) + " for tree:\n" + asString(tree));
  }

  public static int getTreeHeight(Node node) {
    if (node == null) {
      return 0;
    }

    return 1 + Math.max(getTreeHeight(node.getLeft()), getTreeHeight(node.getRight()));
  }
}
