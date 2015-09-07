import support.SimpleTreeSupport;

import java.util.*;

/**
 * Sample output:
 *
 * <code>
 * tree1=
 *     2
 *   7
 *     9
 * 5
 *     11
 *   8
 *     1
 * :: r.siblings={2=9, 7=8, 9=11, 11=1}
 * -
 *
 * tree2=
 *       1
 *     3
 *   5
 * 7
 *   8
 *     9
 *       11
 * :: r.siblings={1=11, 3=9, 5=8}
 * -
 *
 * tree3=
 * 5
 * :: r.siblings={}
 * -
 * </code>
 *
 * @author Alexander Shabanov
 */
public class RightSiblingsDiscovery extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo("tree1", n(5, n(7, n(2), n(9)), n(8, n(11), n(1))));
    demo("tree2", n(7, n(5, n(3, n(1), null), null), n(8, null, n(9, null, n(11)))));
    demo("tree3", n(5));
  }

  private static void demo(String treeName, Node node) {
    System.out.println(treeName + "=\n" + asString(node) + ":: r.siblings=" + getNearestRightSibling(node) + "\n-\n");
  }

  //
  // Link finder
  //

  private static Map<Integer, Integer> getNearestRightSibling(Node root) {
    final Map<Integer, Integer> result = new HashMap<>();
    if (root != null) {
      processSiblings(Collections.singletonList(root), result);
    }
    return result;
  }

  private static void processSiblings(List<Node> siblings, Map<Integer, Integer> target) {
    if (siblings.isEmpty()) {
      return;
    }

    for (int i = 1; i < siblings.size(); ++i) {
      target.put(siblings.get(i - 1).getValue(), siblings.get(i).getValue());
    }

    // construct next layer of siblings - avoid reallocation, so reuse original array
    // implementation note - it is possible to avoid unnecessary reallocations at all if original size of the tree is
    // known - in this case siblings can be modified right here
    final List<Node> nextSiblings = new ArrayList<>();
    for (final Node node : siblings) {
      if (node.getLeft() != null) {
        nextSiblings.add(node.getLeft());
      }
      if (node.getRight() != null) {
        nextSiblings.add(node.getRight());
      }
    }

    processSiblings(nextSiblings, target);
  }
}
