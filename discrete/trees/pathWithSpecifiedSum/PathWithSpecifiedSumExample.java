import support.SimpleTreeSupport;

import java.util.ArrayList;
import java.util.List;

/**
 * Sample run:
 * <pre>
 * Tree=(v: 10, left: (v: 5, left: (v: 4), right: (v: 7)), right: (v: 12))
 * For sum=22 paths=[[10, 5, 7], [10, 12]]
 * For sum=15 paths=[]
 * For sum=19 paths=[[10, 5, 4]]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class PathWithSpecifiedSumExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo1();
  }

  static void demo1() {
    final Node tree = n(10, n(5, n(4), n(7)), n(12));
    System.out.println("Tree=" + tree);

    final List<List<Integer>> paths1 = findPaths(tree, 22);
    System.out.println("For sum=" + 22 + " paths=" + paths1);

    final List<List<Integer>> paths2 = findPaths(tree, 15);
    System.out.println("For sum=" + 15 + " paths=" + paths2);

    final List<List<Integer>> paths3 = findPaths(tree, 19);
    System.out.println("For sum=" + 19 + " paths=" + paths3);
  }

  //
  // Private
  //

  private static List<List<Integer>> findPaths(Node root, int number) {
    final List<List<Integer>> result = new ArrayList<>();
    helperFindPaths(root, 0, number, new ArrayList<>(), result);
    return result;
  }

  private static boolean helperFindPaths(Node current,
                                         int tempSum,
                                         int number,
                                         List<Integer> path,
                                         List<List<Integer>> target) {
    if (current == null) {
      return false;
    }

    final int value = current.getValue();
    final int newSum = value + tempSum;

    path.add(value);

    boolean hasChild = helperFindPaths(current.getLeft(), newSum, number, path, target);
    hasChild = hasChild | helperFindPaths(current.getRight(), newSum, number, path, target);

    if (!hasChild && newSum == number) {
      // leaf node and sum matches the desired one
      target.add(new ArrayList<>(path));
    }

    path.remove(path.size() - 1);
    return true;
  }
}
