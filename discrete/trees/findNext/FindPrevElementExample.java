import support.SimpleTreeSupport;

/**
 * An implementation of an algorithm that finds next element in the tree which is strictly less than the given one.
 *
 * @author Alexander Shabanov
 */
public class FindPrevElementExample extends SimpleTreeSupport {
  public static void main(String[] args) {
    demo("tree1", n(50, n(30, n(10), n(40)), n(70, n(60), n(80))), 10, 30, 55, 75, 80, 85);

    demo("tree2",
        n(80,
            n(40,
                n(20, n(10), n(30)),
                n(60, n(50), n(70))),
            n(120,
                n(100, n(90), n(110)),
                n(140, n(130), n(150)))),
        5, 15, 25, 35, 45, 55, 65, 75, 85, 95, 105, 115, 125, 135, 145, 155);
  }

  //
  // Private
  //

  private static void demo(String treeName, Node node, int... values) {
    System.out.println("----");
    System.out.println(treeName + "=\n" + asString(node));
    for (final int val : values) {
      final Node result = findNodeWithValueLessThan(node, val);
      System.out.println("\tnext for " + val + " = " + (result != null ? result.getValue() : "<none>"));
    }
  }

  private static Node findNodeWithValueLessThan(Node root, int element) {
    if (root == null) {
      return null;
    }

    if (element <= root.getValue()) {
      // element is not greater than current value - go to the left subtree which contains smaller elements
      return findNodeWithValueLessThan(root.getLeft(), element);
    }

    // element is strictly greater than the given one - try to find something in the right subtree
    final Node candidateValue = findNodeWithValueLessThan(root.getRight(), element);
    return candidateValue != null ? candidateValue : root;
  }
}
