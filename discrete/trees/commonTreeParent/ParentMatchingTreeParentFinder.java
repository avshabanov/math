import support.SimpleTreeWithParentSupport;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

public final class ParentMatchingTreeParentFinder extends SimpleTreeWithParentSupport {

  public static void main(String[] args) {
    final Node tree1 = treeFromArray(7, 3, 9, 1, 2, 6, 5, 8, 4);
    System.out.println("Tree:\n" + asString(tree1));
    demo(tree1, 2, 5);
    demo(tree1, 3, 8);
    demo(tree1, 4, 6);
  }

  static void demo(Node tree, Integer left, Integer right) {
    final Node leftNode = tree.lookupByValue(left, Comparator.comparingInt(i -> i));
    final Node rightNode = tree.lookupByValue(right, Comparator.comparingInt(i -> i));
    final Node parent = getClosestCommonParent(leftNode, rightNode);

    System.out.printf(
        "Common parent for nodes %d and %d is %s\n",
        left,
        right,
        (parent != null ? parent.getValue() : "<none>"));
  }

  static Node getClosestCommonParent(Node n1, Node n2) {
    final List<Node> p1 = getParents(n1);
    final List<Node> p2 = getParents(n2);
    Node result = null;
    for (int i1 = p1.size() - 1, i2 = p2.size() - 1; i1 >= 0 && i2 >= 0; --i1, --i2) {
      final Node c1 = p1.get(i1);
      final Node c2 = p2.get(i2);
      if (c1 != c2) {
        break;
      }
      result = c1;
    }

    return result;
  }

  static List<Node> getParents(Node n) {
    final List<Node> result = new ArrayList<>();
    for (; n != null; n = n.getParent()) {
      result.add(n);
    }
    return result;
  }
}
