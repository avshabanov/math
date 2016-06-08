import support.SimpleBtreeSupport;

import java.util.List;

/**
 * https://en.wikipedia.org/wiki/B-tree
 *
 * Properties:
 * <ol>
 * <li>Every node has at most m children.</li>
 * <li>Every non-leaf node (except root) has at least ⌈m/2⌉ children.</li>
 * <li>The root has at least two children if it is not a leaf node.</li>
 * <li>A non-leaf node with k children contains k−1 keys.</li>
 * <li>All leaves appear in the same level</li>
 * </ol>
 *
 * Sample output:
 * <pre>
 * btree[1]=one
 * btree[4]=four
 * btree[1]=uno
 * btree[4]=cuatro
 * Demo #3 - ALL OK, statistics={nodesCreated=223, maxPutDepth=3}, tree.nodeSize=12
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class PrimitiveBtreeExample extends SimpleBtreeSupport {

  public static void main(String[] args) {
    demo1();
    demo2();
    demo3();
  }

  public static void demo1() {
    final Btree<Integer, String> btree = new Btree<>(3);
    btree.put(1, "one");
    btree.put(2, "two");
    btree.put(3, "three");
    btree.put(4, "four");

    System.out.println("btree[1]=" + btree.get(1));
    System.out.println("btree[4]=" + btree.get(4));
  }

  public static void demo2() {
    final Btree<Integer, String> btree = new Btree<>(3);
    btree.put(4, "four");
    btree.put(3, "three");
    btree.put(2, "two");
    btree.put(1, "one");
    btree.put(1, "uno");
    btree.put(3, "tres");
    btree.put(4, "cuatro");

    System.out.println("btree[1]=" + btree.get(1));
    System.out.println("btree[4]=" + btree.get(4));
  }

  public static void demo3() {
    final RandomShuffleResult<Btree<Integer, String>> randomShuffleResult = createRandomShuffleBtree(1000,
        () -> new Btree<>(12));
    final Btree<Integer, String> btree = randomShuffleResult.getBtree();
    final List<KeyValue<Integer, String>> pairs = randomShuffleResult.getPairs();

    // verify values
    for (final KeyValue<Integer, String> kv : pairs) {
      final String v = btree.get(kv.getKey());
      if (!kv.getValue().equals(v)) {
        throw new AssertionError("mismatch for key=" + kv.getKey());
      }
    }

    System.out.println("Demo #3 - ALL OK, statistics=" + btree.getStatistics() +
        ", tree.nodeSize=" + btree.getNodeSize());
  }
}
