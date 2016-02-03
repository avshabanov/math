import support.SimpleTreeSupport;

import java.util.ArrayDeque;
import java.util.Deque;

/**
 * Sample run:
 * <pre>
 * ---
 * Node count=0 for tree:
 * (null)
 * ---
 * Node count=1 for tree:
 * 1
 *
 * ---
 * Node count=3 for tree:
 *   1
 * 2
 *   3
 *
 * ---
 * Node count=7 for tree:
 *     10
 *   25
 *     30
 * 50
 *     60
 *   75
 *     80
 *
 * ---
 * Node count=9 for tree:
 *         1
 *       2
 *     3
 *   4
 * 5
 *   6
 *     7
 *       8
 *         9
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class TreeNodeCountExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(null, 0);
    demo(n(1), 1);
    demo(n(2, n(1), n(3)), 3);
    demo(treeFromArray(50, 25, 75, 10, 30, 60, 80), 7);
    demo(treeFromArray(5, 4, 6, 3, 7, 2, 8, 1, 9), 9);
  }

  public static void demo(Node node, int expectedCount) {
    System.out.println("---\nNode count=" + expectedCount + " for tree:\n" + asString(node));
    if (expectedCount != getNodeCountRecursive(node)) {
      throw new AssertionError("Unexpected result from getNodeCountRecursive");
    }
    if (expectedCount != getNodeCountNonRecursive(node)) {
      throw new AssertionError("Unexpected result from getNodeCountRecursive");
    }
  }

  public static int getNodeCountRecursive(Node node) {
    if (node == null) {
      return 0;
    }

    return 1 + getNodeCountRecursive(node.getLeft()) + getNodeCountRecursive(node.getRight());
  }

  public static int getNodeCountNonRecursive(Node node) {
    final Deque<Node> nodes = new ArrayDeque<>();
    if (node != null) {
      nodes.add(node);
    }

    int result = 0;
    while (!nodes.isEmpty()) {
      final Node n = nodes.removeLast();
      ++result;
      if (n.getRight() != null) {
        nodes.add(n.getRight());
      }
      if (n.getLeft() != null) {
        nodes.add(n.getLeft());
      }
    }

    return result;
  }
}
