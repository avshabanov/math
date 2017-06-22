import support.SimpleTreeSupport;

import java.util.List;
import java.util.Optional;

/**
 * @author Alexander Shabanov
 */
public final class FindNextElementRecursiveExample2 extends SimpleTreeSupport {
  public static void main(String[] args) {
    demo("tree1",
        n(50,
          n(30, n(10), n(40)),
          n(70, n(60), n(80))),
        30, 55, 75, 80, 85);
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
    final List<Integer> treeValues = node.toList();
    for (final int val : values) {
      final Node result = findNodeWithValueGreaterThan(node, val);
      final Optional<Integer> actualNext = treeValues.stream().filter(i -> i > val).findFirst();
      if (((result != null) && (!actualNext.isPresent() || !actualNext.get().equals(result.getValue()))) ||
          ((result == null) && actualNext.isPresent())) {
        throw new AssertionError("Mismatch for value=" + val);
      }
      System.out.println("\tnext for " + val + " = " + (result != null ? result.getValue() : "<none>"));
    }
  }

  private static Node findNodeWithValueGreaterThan(Node root, int element) {
    if (root == null) {
      return null;
    }

    Node candidate = findNodeWithValueGreaterThan(root.getLeft(), element);
    if (candidate != null) {
      return candidate;
    }
    if (element < root.getValue()) {
      return root;
    }
    return findNodeWithValueGreaterThan(root.getRight(), element);
  }
}
