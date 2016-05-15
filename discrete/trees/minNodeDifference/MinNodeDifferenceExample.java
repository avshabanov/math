import support.SimpleTreeSupport;

import java.util.ArrayDeque;
import java.util.Deque;

/**
 * Sample run:
 * <pre>
 * Min node diff=2 in a tree=
 *   5
 * 10
 *     12
 *   16
 *     20
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class MinNodeDifferenceExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(treeFromArray(10, 5, 16, 12, 20));
  }

  public static void demo(Node root) {
    System.out.println("Min node diff=" + findMinNodeDifference(root) + " in a tree=\n" + asString(root));
  }

  public static int findMinNodeDifference(Node root) {
    final Deque<Node> nodes = new ArrayDeque<>();
    addLeftSubtree(root, nodes);

    int minDiff = Integer.MAX_VALUE;
    int prev = 0;

    for (boolean next = false; !nodes.isEmpty(); next = true) {
      final Node node = nodes.pop();
      final int value = node.getValue();
      //System.out.println("[DBG] node.v=" + value);
      if (next) {
        final int diff = value - prev;
        minDiff = Math.min(diff, minDiff);
      }
      prev = value;

      final Node right = node.getRight();
      addLeftSubtree(right, nodes);
    }

    return minDiff;
  }

  private static void addLeftSubtree(Node node, Deque<Node> target) {
    for (Node it = node; it != null; it = it.getLeft()) {
      target.push(it);
    }
  }
}
