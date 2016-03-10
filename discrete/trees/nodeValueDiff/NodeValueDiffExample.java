import support.SimpleTreeSupport;

import java.util.Optional;

/**
 * Sample run:
 * <pre>
 * Min diff value=None in a tree:
 * Disconnected from the target VM, address: '127.0.0.1:50002', transport: 'socket'
 * (null)
 * Min diff value=None in a tree:
 * 1
 *
 * Min diff value=10 in a tree:
 *   10
 * 20
 *   40
 *
 * Min diff value=2 in a tree:
 *   10
 *     12
 * 20
 *   40
 *
 * Min diff value=3 in a tree:
 *     10
 *       20
 *   30
 * 50
 *     60
 *   70
 *     80
 *       85
 *         88
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class NodeValueDiffExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(null);
    demo(n(1));
    demo(treeFromArray(20, 10, 40));
    demo(treeFromArray(20, 10, 40, 12));
    demo(treeFromArray(50, 30, 70, 10, 20, 60, 80, 85, 88));
  }

  public static void demo(Node tree) {
    final Optional<Integer> value = findMinDiffValue(tree);
    System.out.println("Min diff value=" + (value.isPresent() ? value.get() : "None") +
        " in a tree:\n" + asString(tree));
  }

  public static Optional<Integer> findMinDiffValue(Node tree) {
    final DiffFinder finder = new DiffFinder();
    finder.find(null, tree);
    return finder.found ? Optional.of(finder.minDiff) : Optional.empty();
  }

  public static final class DiffFinder {
    int minDiff = Integer.MAX_VALUE; // use unboxed type to avoid unnecessary boxing/unboxing
    boolean found = false;

    public void find(Node parent, Node sibling) {
      if (sibling == null) {
        return;
      }

      if (parent != null) {
        minDiff = Math.min(minDiff, Math.abs(sibling.getValue() - parent.getValue()));
        found = true;
      }

      find(sibling, sibling.getLeft());
      find(sibling, sibling.getRight());
    }
  }
}
