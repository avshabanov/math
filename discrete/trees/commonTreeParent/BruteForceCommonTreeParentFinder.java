import support.SimpleTreeWithParentSupport;

import java.util.Comparator;

/**
 * Problem:
 * <pre>
 *   Given the tree where each node has a link to the parent, write a function that finds common parent for two given
 *   nodes.
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class BruteForceCommonTreeParentFinder extends SimpleTreeWithParentSupport {

  public static void main(String[] args) {
    final Node tree1 = treeFromArray(7, 3, 9, 1, 2, 6, 5, 8, 4);
    System.out.println("Tree:\n" + asString(tree1));
    demo(tree1, 2, 5);
    demo(tree1, 3, 8);
    demo(tree1, 4, 6);

    final Node tree2 = treeFromArray(
        50,
        25, 75,
        12, 37, 62, 87,
        6, 18, 31, 43, 56, 68, 81, 93,
        4, 8, 16, 20, 29, 33, 40, 45, 54, 58, 65, 70, 79, 83, 90, 95,
        1, 5, 94, 97
    );
    System.out.println("---\nTree:\n" + asString(tree2));
    demo(tree2, 1, 97);
    demo(tree2, 18, 40);
    demo(tree2, 70, 93);
    demo(tree2, 45, 54);
  }

  private static void demo(Node tree, int left, int right) {
    final Node leftNode = tree.lookupByValue(left, Comparator.comparingInt(i -> i));
    final Node rightNode = tree.lookupByValue(right, Comparator.comparingInt(i -> i));
    final Node parent = getClosestCommonParent(leftNode, rightNode);

    System.out.printf(
        "Common parent for nodes %d and %d is %s\n",
        left,
        right,
        (parent != null ? parent.getValue() : "<none>"));
  }

  private static Node getClosestCommonParent(Node left, Node right) {
    NodeDistance closestParent = getClosestNode(left, right, 0);
    return closestParent != null ? closestParent.node : null;

//    if (left == null || right == null) {
//      return null;
//    }
//
//    if (left == right) {
//      return left;
//    }
//
//    Node result = getClosestCommonParent(left.getParent(), right);
//    if (result != null) {
//      return result;
//    }
//
//    result = getClosestCommonParent(left, right.getParent());
//    if (result != null) {
//      return result;
//    }
//
//    return getClosestCommonParent(left.getParent(), right.getParent());
  }

  private static NodeDistance getClosestNode(Node left, Node right, int distance) {
    if (left == null || right == null) {
      return null;
    }

    if (left == right) {
      return new NodeDistance(left, distance);
    }

    NodeDistance closestParent = getClosestNode(left.getParent(), right, distance + 1);
    NodeDistance other = getClosestNode(left, right.getParent(), distance + 1);
    if (closestParent == null || (other != null && other.distance < closestParent.distance)) {
      closestParent = other;
    }

    other = getClosestNode(left.getParent(), right.getParent(), distance + 2);
    if (closestParent == null || (other != null && other.distance < closestParent.distance)) {
      closestParent = other;
    }

    return closestParent;
  }

  private static final class NodeDistance {
    final Node node;
    final int distance;

    public NodeDistance(Node node, int distance) {
      this.node = node;
      this.distance = distance;
    }
  }
}
