import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;
import java.util.Queue;

/**
 * Examples of BFS and DFS for a binary search tree -
 * acyclic directed graph where each vertex is connected with at most two other vertices and
 * each but one vertex has exactly one other vertex which is connected with it.
 *
 * @author Alexander Shabanov
 */
public final class BinaryTreeTraversalExample {

  public static void main(String[] args) {
    final SimpleBinaryTree<Integer> tree = new SimpleBinaryTree<>();
    tree.add(5).add(3).add(7);
    System.out.println("[3<-5->7] tree =\n" + tree + ":: dfs=" + dfs(tree) + "\n" +
        ":: bfs=" + bfs(tree) + "\n");

    tree.add(2).add(4).add(6).add(8).add(1).add(9);
    System.out.println("[1,3,4<-5->6,7,8] tree =\n" + tree + ":: dfs=" + dfs(tree) + "\n" +
        ":: bfs=" + bfs(tree) + "\n");
  }

  //
  // Breadth-First Search
  //

  public static <TKey extends Comparable<TKey>> List<TKey> bfs(SimpleBinaryTree<TKey> tree) {
    final List<TKey> result = new ArrayList<>();

    final Queue<SimpleBinaryTree.Node<TKey>> nodesQueue = new ArrayDeque<>();
    if (tree.root != null) {
      nodesQueue.add(tree.root);
    }

    while (!nodesQueue.isEmpty()) {
      final int size = nodesQueue.size();

      // empty current slice and insert next one
      for (int i = 0; i < size; ++i) {
        final SimpleBinaryTree.Node<TKey> node = nodesQueue.remove();
        result.add(node.key);
        if (node.left != null) {
          nodesQueue.add(node.left);
        }
        if (node.right != null) {
          nodesQueue.add(node.right);
        }
      }
    }

    return result;
  }

  //
  // Depth-First Search
  //

  public static <TKey extends Comparable<TKey>> List<TKey> dfs(SimpleBinaryTree<TKey> tree) {
    final List<TKey> result = new ArrayList<>();
    dfsStep(tree.root, result);
    return result;
  }

  private static <TKey extends Comparable<TKey>> void dfsStep(SimpleBinaryTree.Node<TKey> node, List<TKey> result) {
    if (node == null) {
      return;
    }

    result.add(node.key);
    dfsStep(node.left, result);
    dfsStep(node.right, result);
  }

  //
  // Tree Definition
  //

  /**
   * Simple intrusive tree, no balancing.
   */
  private static final class SimpleBinaryTree<TKey extends Comparable<TKey>> {
    private static final class Node<TKey> {
      private final TKey key;
      private Node<TKey> left;
      private Node<TKey> right;

      public Node(TKey key) {
        this.key = key;
      }
    }

    private Node<TKey> root;

    // inserts a new node without balancing, allows duplicates
    public SimpleBinaryTree<TKey> add(TKey key) {
      final Node<TKey> newNode = new Node<>(key);

      if (root == null) {
        root = newNode;
      } else {
        Node<TKey> candidate = root;
        for (;;) {
          final int comparisonResult = key.compareTo(candidate.key);
          if (comparisonResult > 0) {
            if (candidate.right != null) {
              candidate = candidate.right;
              continue;
            }

            candidate.right = newNode;
            break;
          }

          if (candidate.left != null) {
            candidate = candidate.left;
            continue;
          }

          candidate.left = newNode;
          break;
        }
      }

      return this;
    }

    @Override
    public String toString() {
      final StringBuilder builder = new StringBuilder(100);
      appendTo(0, root, builder);
      return builder.toString();
    }

    private static void appendTo(int indent, Node<?> node, StringBuilder target) {
      if (node == null) {
        for (int i = 0; i < indent; ++i) {
          target.append(' ');
        }
        target.append("(null)").append('\n');
        return;
      }
      appendTo(indent + 1, node.left, target);
      for (int i = 0; i < indent; ++i) {
        target.append(' ');
      }
      target.append('(').append(node.key).append(')').append('\n');
      appendTo(indent + 1, node.right, target);
    }
  }
}
