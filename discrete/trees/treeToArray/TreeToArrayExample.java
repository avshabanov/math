import support.SimpleTreeSupport;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;


/**
 * Sample run:
 * <pre>
 * Tree array=[] for tree:
 * (null)
 *
 * Tree array=[1] for tree:
 * 1
 *
 *
 * Tree array=[1, 2, 3] for tree:
 *   1
 * 2
 *   3
 *
 *
 * Tree array=[12, 14, 15, 17, 18, 20, 25, 30, 35, 40, 50] for tree:
 *     12
 *       14
 *   15
 *       17
 *     18
 * 20
 *       25
 *     30
 *       35
 *   40
 *     50
 *
 *
 * Tree array=[1, 2, 3, 4, 5, 6, 7, 8, 9] for tree:
 *         1
 *       2
 *     3
 *   4
 * 5
 *   6
 *     7
 *       8
 *         9
 *
 *
 * Tree array=[1, 2, 3, 4, 5, 6, 7, 8, 9] for tree:
 *       1
 *     2
 *       3
 *   4
 *       5
 *     6
 * 7
 *     8
 *   9
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class TreeToArrayExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(null);
    demo(n(1));
    demo(n(2, n(1), n(3)));
    demo(treeFromArray(20, 15, 40, 12, 18, 30, 50, 14, 17, 25, 35));
    demo(treeFromArray(5, 4, 6, 3, 7, 2, 8, 1, 9));
    demo(treeFromArray(7, 4, 9, 2, 6, 8, 1, 3, 5));
  }

  private static void demo(Node node) {
    final List<Integer> result1 = Simplest.toArray(node);
    final int[] r2 = Optimal.toArray(node);
    final List<Integer> result2 = IntStream.of(r2).boxed().collect(Collectors.toList());
    if (!result2.equals(result1)) {
      throw new AssertionError("Array mismatch result1=" + result1 + ", result2=" + result2);
    }
    System.out.println("Tree array=" + result1 + " for tree:\n" + asString(node) + "\n");
  }

  //
  // Private
  //

  private static final class Simplest {

    // simplest way of converting a tree to array
    static List<Integer> toArray(Node node) {
      final List<Integer> result = new ArrayList<>();
      addRecursively(node, result);
      return result;
    }

    private static void addRecursively(Node node, List<Integer> result) {
      if (node == null) {
        return;
      }

      addRecursively(node.getLeft(), result);
      result.add(node.getValue());
      addRecursively(node.getRight(), result);
    }
  }

  private static final class Optimal {
    static int[] toArray(final Node node) {
      final Deque<Node> nodes = new ArrayDeque<>();
      if (node != null) {
        nodes.add(node);
      }

      // get node count
      int nodeCount = 0;
      while (!nodes.isEmpty()) {
        final Node n = nodes.removeLast();
        ++nodeCount;
        if (n.getRight() != null) {
          nodes.add(n.getRight());
        }
        if (n.getLeft() != null) {
          nodes.add(n.getLeft());
        }
      }

      // prepare resultant array
      final int arr[] = new int[nodeCount];

      // add node to the array
      int index = nodeCount;
      addRightNodesToDeque(nodes, node);
      while (!nodes.isEmpty()) {
        final Node n = nodes.removeLast();

        --index;
        arr[index] = n.getValue();

        if (n.getLeft() != null) {
          addRightNodesToDeque(nodes, n.getLeft());
        }
      }

      return arr;
    }

    static void addRightNodesToDeque(Deque<Node> nodes, Node node) {
      for (Node n = node; n != null; n = n.getRight()) {
        nodes.add(n);
      }
    }
  }
}
