import support.SimpleTreeSupport;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Sample run:
 * <pre>
 * Min path=[] in a tree:
 * (null)
 * Min path=[1] in a tree:
 * 1
 *
 * Min path=[2, 1] in a tree:
 *   1
 * 2
 *   3
 *
 * Min path=[2, 3, 1] in a tree:
 *     25
 *   1
 * 2
 *     4
 *   3
 *     1
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class FindMinPathExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(null);
    demo(n(1));
    demo(n(2, n(1), n(3)));
    demo(n(2, n(1, n(25), null), n(3, n(4), n(1))));
  }

  public static void demo(Node root) {
    System.out.println("Min path=" + findMinPath(root) + " in a tree:\n" + asString(root));
  }

  private static List<Integer> findMinPath(Node root) {
    if (root == null) {
      return Collections.emptyList();
    }

    final Finder finder = new Finder();
    finder.find(root, new ArrayList<>(), 0);
    return finder.minPath;
  }

  private static final class Finder {
    private int pathLen;
    private List<Integer> minPath;

    public void find(Node node, List<Integer> nodes, int curPath) {
      final int length = nodes.size();
      final int value = node.getValue();
      curPath += value;
      nodes.add(value);

      if (node.getLeft() != null) {
        find(node.getLeft(), nodes, curPath);
      }

      if (node.getRight() != null) {
        find(node.getRight(), nodes, curPath);
      }

      if (node.getLeft() == null && node.getRight() == null) {
        // no left or right nodes
        if (curPath < pathLen || minPath == null) {
          pathLen = curPath;
          minPath = new ArrayList<>(nodes);
        }
      }

      nodes.remove(length);
    }
  }
}
