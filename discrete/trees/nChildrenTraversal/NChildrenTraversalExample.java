import support.SimpleBtreeSupport;

import java.util.ArrayList;
import java.util.List;

/**
 * Sample run:
 *
 * <pre>
 * btree iter=[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class NChildrenTraversalExample extends SimpleBtreeSupport {

  public static void main(String[] args) {
    demo1();
  }

  public static void demo1() {
    final RandomShuffleResult randomShuffleResult = createRandomShuffleBtree(10, 3);

    final List<Integer> iterResult = iterate(randomShuffleResult.getBtree());

    System.out.println("btree iter=" + iterResult);
  }

  private static List<Integer> iterate(Btree<Integer, String> btree) {
    final List<Integer> result = new ArrayList<>();
    recursiveIterHelper(btree.getRoot(), result);
    return result;
  }

  private static void recursiveIterHelper(Node<Integer, String> node, List<Integer> result) {
    if (node == null) {
      return;
    }

    for (int i = 0; i < node.getSize(); ++i) {
      recursiveIterHelper(node.getChildren()[i], result);
      result.add(node.getKeyValues()[i].getKey());
    }

    recursiveIterHelper(node.getChildren()[node.getSize()], result);
  }

}
