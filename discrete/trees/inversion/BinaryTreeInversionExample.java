import support.SimpleTreeSupport;

/**
 * Example of binary tree inversion (i.e. mirroring a binary tree).
 *
 * Sample output:
 * <pre>
 * Source tree=
 *     10
 *   25
 *     30
 * 50
 *     60
 *   75
 *     80
 *
 * Inverted tree=
 *     80
 *   75
 *     60
 * 50
 *     30
 *   25
 *     10
 * </pre>
 */
public final class BinaryTreeInversionExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    final Node tree = treeFromArray(50, 25, 75, 10, 30, 60, 80);
    System.out.println("Source tree=\n" + asString(tree));
    invert(tree);
    System.out.println("Inverted tree=\n" + asString(tree));
  }

  //
  // Private
  //

  private static void invert(Node node) {
    if (node == null) {
      return;
    }

    final Node left = node.getLeft();
    final Node right = node.getRight();

    node.setLeft(right);
    node.setRight(left);

    invert(left);
    invert(right);
  }
}
