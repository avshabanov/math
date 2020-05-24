import support.SimpleTreeSupport;

import java.util.ArrayList;
import java.util.List;

/**
 * Sample run:
 * <pre>
 * ---
 * Tree=
 *     10
 *   30
 *     40
 * 50
 *     60
 *   70
 *     80
 *
 * Elements greater than key=15 with offset=1, limit=10 are: [40, 50, 60, 70, 80]
 * Elements greater than key=45 with offset=0, limit=1 are: [50]
 * ---
 * Tree=
 *   30
 * 40
 *       50
 *     60
 *         65
 *       70
 *         75
 *   80
 *     90
 *
 * Elements greater than key=70 with offset=0, limit=4 are: [75, 80, 90]
 * Elements greater than key=70 with offset=2, limit=1 are: [90]
 * Elements greater than key=95 with offset=2, limit=1 are: []
 * Elements greater than key=10 with offset=0, limit=1 are: [30]
 * Elements greater than key=10 with offset=8, limit=1 are: [90]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class OffsetLimitExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    final Node tree1 = n(50, n(30, n(10), n(40)), n(70, n(60), n(80)));
    System.out.println("---\nTree=\n" + asString(tree1));

    demo(tree1, 15, 1, 10);
    demo(tree1, 45, 0, 1);

    System.out.println("---\nTree=\n" + asString(n(10)));
    demo(n(10), 9, 0, 10);

    final Node tree2 = n(40,
        n(30),
        n(80,
            n(60, n(50), n(70, n(65), n(75))),
            n(90)));
    System.out.println("---\nTree=\n" + asString(tree2));

    demo(tree2, 70, 0, 4);
    demo(tree2, 70, 2, 1);
    demo(tree2, 95, 2, 1);
    demo(tree2, 10, 0, 1);
    demo(tree2, 10, 8, 1);
  }

  public static void demo(Node tree, int key, int offset, int limit) {
    System.out.println("Elements greater than key=" + key + " with offset=" + offset +
        ", limit=" + limit + " are: " + find(tree, key, offset, limit));
  }

  public static List<Integer> find(Node root, int key, int offset, int limit) {
    final List<Integer> result = new ArrayList<>();
    final Solver solver = new Solver(result, key, offset, limit);
    solver.collect(root, 0);
    return result;
  }

  //
  // Private
  //

  private static final class Solver {
    final List<Integer> collector;
    final int key;
    final int offset;
    final int limit;

    public Solver(List<Integer> collector, int key, int offset, int limit) {
      this.collector = collector;
      this.key = key;
      this.offset = offset;
      this.limit = limit;
    }

    int collect(final Node node, final int foundPos) {
      if (node == null) {
        return foundPos;
      }

      if (foundPos > (offset + limit)) {
        return foundPos; // do not attempt to search further if all the elements have been found
      }

      int nextPos = foundPos;
      if (node.getValue() > key) {
        nextPos = collect(node.getLeft(), foundPos);
        if (nextPos >= offset && (nextPos < (offset + limit))) {
          collector.add(node.getValue()); // this node value is within the desired range
        }

        nextPos = nextPos + 1;
      }

      return collect(node.getRight(), nextPos);
    }
  }
}
