import support.SimpleTreeSupport;

/**
 * An implementation of an algorithm that finds next element in the tree which is strictly greater than the given one.
 *
 * Sample output:
 * <code>
 * tree1=
 *     10
 *   30
 *     40
 * 50
 *     60
 *   70
 *     80
 *
 * 	next for 30 = 40
 * 	next for 55 = 60
 * 	next for 75 = 80
 * 	next for 80 = &lt;none&gt;
 * 	next for 85 = &lt;none&gt;
 * tree2=
 *       10
 *     20
 *       30
 *   40
 *       50
 *     60
 *       70
 * 80
 *       90
 *     100
 *       110
 *   120
 *       130
 *     140
 *       150
 *
 * 	next for 5 = 10
 * 	next for 15 = 20
 * 	next for 25 = 30
 * 	next for 35 = 40
 * 	next for 45 = 50
 * 	next for 55 = 60
 * 	next for 65 = 70
 * 	next for 75 = 80
 * 	next for 85 = 90
 * 	next for 95 = 100
 * 	next for 105 = 110
 * 	next for 115 = 120
 * 	next for 125 = 130
 * 	next for 135 = 140
 * 	next for 145 = 150
 * 	next for 155 = &lt;none&gt;
 * </code>
 *
 * @author Alexander Shabanov
 */
public final class FindNextElementExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo("tree1", n(50, n(30, n(10), n(40)), n(70, n(60), n(80))), 30, 55, 75, 80, 85);
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
    System.out.println(treeName + "=\n" + asString(node));
    for (final int val : values) {
      final Node result = findNodeWithValueGreaterThan(node, val);
      System.out.println("\tnext for " + val + " = " + (result != null ? result.getValue() : "<none>"));
    }
  }

  private static Node findNodeWithValueGreaterThan(Node root, int element) {
    if (root == null) {
      return null;
    }

    if (element >= root.getValue()) {
      // element is not smaller than current value - go to the right subtree which contains greater elements
      return findNodeWithValueGreaterThan(root.getRight(), element);
    }

    // element is strictly less than the given one - try to find something in the left subtree
    final Node candidateValue = findNodeWithValueGreaterThan(root.getLeft(), element);
    return candidateValue != null ? candidateValue : root;
  }
}
