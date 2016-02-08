import support.SimpleTreeSupport;

import java.util.*;

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
    demo(treeFromArray(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));
  }

  public static void demo(Node tree) {
    final Map<Integer, Integer> result = getLevelMapRecursive(tree);

    if (!result.equals(getLevelMapNonRecursive(tree))) {
      throw new AssertionError("getLevelMapNonRecursive returned wrong result");
    }

    if (!result.equals(getLevelMapNonRecursive2(tree))) {
      throw new AssertionError("getLevelMapNonRecursive2 returned wrong result");
    }

    System.out.println("Level map=" + result + " for tree:\n" + asString(tree));
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

  // O(height(tree)) memory complexity
  public static Map<Integer, Integer> getLevelMapNonRecursive(Node tree) {
    final Deque<NonRecursiveLevelEntry> entries = new ArrayDeque<>();
    final Map<Integer, Integer> result = new HashMap<>();
    if (tree != null) {
      entries.add(new NonRecursiveLevelEntry(tree, 0));
    }

    while (!entries.isEmpty()) {
      final NonRecursiveLevelEntry entry = entries.removeLast();
      final int level = entry.level;
      final Node node = entry.node;

      result.put(node.getValue(), level);

      final int newLevel = level + 1;
      if (node.getLeft() != null) {
        entries.add(new NonRecursiveLevelEntry(node.getLeft(), newLevel));
      }
      if (node.getRight() != null) {
        entries.add(new NonRecursiveLevelEntry(node.getRight(), newLevel));
      }
    }

    return result;
  }

  private static final class NonRecursiveLevelEntry {
    final Node node;
    final int level;

    public NonRecursiveLevelEntry(Node node, int level) {
      this.node = node;
      this.level = level;
    }
  }

  // O(width(tree)) memory complexity, no additional class (similar to NonRecursiveLevelEntry from the previous
  // non-recursive solution.
  public static Map<Integer, Integer> getLevelMapNonRecursive2(Node tree) {
    final Deque<Node> nodes = new ArrayDeque<>();
    final Map<Integer, Integer> result = new HashMap<>();
    int level = 0;
    if (tree != null) {
      nodes.add(tree);
    }

    while (!nodes.isEmpty()) {
      final int size = nodes.size();
      for (int i = 0; i < size; ++i) {
        final Node node = nodes.removeFirst();

        result.put(node.getValue(), level);

        if (node.getLeft() != null) {
          nodes.add(node.getLeft());
        }

        if (node.getRight() != null) {
          nodes.add(node.getRight());
        }
      }

      ++level;
    }

    return result;
  }
}
