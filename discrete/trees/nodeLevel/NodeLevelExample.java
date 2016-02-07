import support.SimpleTreeSupport;

import java.util.HashMap;
import java.util.Map;

/**
 * Sample run:
 * <pre>
 * Level map={} for tree:
 * (null)
 * Level map={1=0} for tree:
 * 1
 *
 * Level map={1=1, 2=0, 3=1} for tree:
 *   1
 * 2
 *   3
 *
 * Level map={1=2, 2=3, 3=1, 5=0, 6=2, 7=1, 8=2, 9=4, 10=3, 11=4, 12=5} for tree:
 *     1
 *       2
 *   3
 * 5
 *     6
 *   7
 *     8
 *         9
 *       10
 *         11
 *           12
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class NodeLevelExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(null);
    demo(n(1));
    demo(treeFromArray(2, 1, 3));
    demo(treeFromArray(5, 3, 7, 1, 2, 6, 8, 10, 9, 11, 12));
  }

  public static void demo(Node tree) {
    System.out.println("Level map=" + getLevelMapRecursive(tree) + " for tree:\n" + asString(tree));
  }

  public static Map<Integer, Integer> getLevelMapRecursive(Node tree) {
    final Map<Integer, Integer> levelMap = new HashMap<>();
    visit(tree, 0, levelMap);
    return levelMap;
  }

  private static void visit(Node node, int level, Map<Integer, Integer> levelMap) {
    if (node == null) {
      return;
    }

    levelMap.put(node.getValue(), level);
    visit(node.getLeft(), level + 1, levelMap);
    visit(node.getRight(), level + 1, levelMap);
  }

  // TODO: non-recursive solution
}
