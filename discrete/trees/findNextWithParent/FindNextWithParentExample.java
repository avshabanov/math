import support.SimpleTreeWithParentSupport;

/**
 * Another example of finding next element (parent link is actually unused here).
 *
 * @author Alexander Shabanov
 */
public final class FindNextWithParentExample extends SimpleTreeWithParentSupport {

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

  private static void demo(String treeName, Node node, int... values) {
    System.out.println(treeName + "=\n" + asString(node));
    for (final int val : values) {
      final Node result = findNodeWithValueGreaterThan(node, val);
      System.out.println("\tnext for " + val + " = " + (result != null ? result.getValue() : "<none>"));
    }
  }

  public static Node findNodeWithValueGreaterThan(Node node, int value) {
    Node candidate = null;

    for (Node it = node; it != null;) {
      if (it.getValue() > value) {
        candidate = it;
        // search on the left subtree
        it = it.getLeft();
        continue;
      }

      it = it.getRight();
    }

    return candidate;
  }
}
