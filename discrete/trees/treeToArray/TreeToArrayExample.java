import support.SimpleTreeSupport;

import java.util.ArrayList;
import java.util.List;


/**
 * Sample run:
 * <pre>
 * [Simplest] result=[]
 * [Simplest] result=[1]
 * [Simplest] result=[1, 2, 3]
 * [Simplest] result=[12, 14, 15, 17, 18, 20, 25, 30, 35, 40, 50]
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
  }

  private static void demo(Node node) {
    final List<Integer> r = Simplest.toArray(node);
    System.out.println("[Simplest] result=" + r);
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
}
