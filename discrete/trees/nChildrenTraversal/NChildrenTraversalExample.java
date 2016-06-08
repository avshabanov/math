import support.SimpleBtreeSupport;

import java.util.*;

/**
 * Sample run:
 *
 * <pre>
 * [1] btree iter=[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
 * [2] btree iter=[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
 * [3] btree iter=[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class NChildrenTraversalExample extends SimpleBtreeSupport {

  public static void main(String[] args) {
    demo1();
    demo2();
    demo3();
  }

  public static void demo1() {
    final RandomShuffleResult<Btree<Integer, String>> randomShuffleResult = createRandomShuffleBtree(10,
        () -> new Btree<>(3));

    final List<Integer> iterResult = iterate(randomShuffleResult.getBtree());

    System.out.println("[1] btree iter=" + iterResult);
  }

  public static void demo2() {
    final RandomShuffleResult<Btree<Integer, String>> randomShuffleResult = createRandomShuffleBtree(10,
        () -> new Btree<>(3));

    final List<Integer> iterResult = nonRecursiveIterate(randomShuffleResult.getBtree());

    System.out.println("[2] btree iter=" + iterResult);
  }

  public static void demo3() {
    final RandomShuffleResult<SimpleIterableBtree<Integer, String>> randomShuffleResult = createRandomShuffleBtree(10,
        () -> new SimpleIterableBtree<>(3));

    final List<Integer> iterResult = new ArrayList<>();
    randomShuffleResult.getBtree().entryIterator().forEachRemaining(e -> iterResult.add(e.getKey()));

    System.out.println("[3] btree iter=" + iterResult);
  }

  //
  // Recursive solution
  //

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

  //
  // Non-recursive solution #1
  //

  private static <K extends Comparable<K>, V>
  List<K> nonRecursiveIterate(Btree<K, V> btree) {
    final List<K> result = new ArrayList<>();

    final Deque<BtreeIterator.IterEntry<K, V>> deque = new ArrayDeque<>();
    if (btree.getRoot() != null) {
      deque.push(new BtreeIterator.IterEntry<>(btree.getRoot(), 0));
    }

    // iterate over the list
    while (!deque.isEmpty()) {
      final BtreeIterator.IterEntry<K, V> entry = deque.pop();
      final int pos = entry.index / 2;
      entry.index = entry.index + 1;

      // do we need to keep processing this node?
      if (pos < entry.node.size()) {
        deque.push(entry);
      }

      // is it a value?
      if ((entry.index & 1) == 0) {
        assert pos < entry.node.size();
        final KeyValue<K, V> kv = entry.node.getKeyValues()[pos];
        if (kv == null) {
          throw new IllegalStateException("kv == null");
        }

        result.add(kv.getKey());
        continue;
      }

      // not a value, add this node to the stack
      final Node<K, V> childNode = entry.node.getChildren()[pos];
      if (childNode != null && childNode.size() > 0) {
        deque.push(new BtreeIterator.IterEntry<>(childNode, 0));
      }
    }

    return result;
  }

  //
  // Non-recursive solution #2
  //

  private static final class SimpleIterableBtree<K extends Comparable<K>, V>
      extends Btree<K, V> {

    public SimpleIterableBtree(int nodeSize) {
      super(nodeSize);
    }

    Iterator<Map.Entry<K, V>> entryIterator() {
      return new BtreeIterator<>(root);
    }
  }

  private static final class BtreeIterator<K extends Comparable<K>, V> implements Iterator<Map.Entry<K, V>> {
    private final Deque<IterEntry<K, V>> deque = new ArrayDeque<>();

    public BtreeIterator(Node<K, V> root) {
      if (root != null && root.size() > 0) {
        deque.add(new IterEntry<>(root, 0));
      }
    }

    @Override
    public boolean hasNext() {
      return deque.size() > 0;
    }

    @Override
    public Map.Entry<K, V> next() {
      if (deque.isEmpty()) {
        throw new NoSuchElementException();
      }

      for (;;) {
        final BtreeIterator.IterEntry<K, V> entry = deque.pop();
        final int pos = entry.index / 2;
        entry.index = entry.index + 1;

        // do we need to keep processing this node?
        if (pos < entry.node.size()) {
          deque.push(entry);
        }

        // is it a value?
        if ((entry.index & 1) == 0) {
          assert pos < entry.node.size();
          final KeyValue<K, V> kv = entry.node.getKeyValues()[pos];
          if (kv == null) {
            throw new IllegalStateException("kv == null");
          }

          clearStack();
          return new AbstractMap.SimpleImmutableEntry<>(kv.getKey(), kv.getValue());
        }

        // not a value, add this node to the stack
        final Node<K, V> childNode = entry.node.getChildren()[pos];
        if (childNode != null && childNode.size() > 0) {
          deque.push(new BtreeIterator.IterEntry<>(childNode, 0));
        }
      }
    }

    //
    // Private
    //

    /**
     * Clears a stack if processing came to an end, to produce the right response in {@link #hasNext()} function.
     */
    private void clearStack() {
      while (!deque.isEmpty()) {
        final IterEntry<K, V> e = deque.getLast();
        if (e.index != (e.node.size() * 2)) {
          return;
        }

        if (e.node.getChildren()[e.node.size()] != null) {
          return;
        }

        deque.removeLast();
      }
    }

    private static final class IterEntry<K extends Comparable<K>, V> {
      private final Node<K, V> node;
      private int index; // even values are corresponding to children, odd ones - to values

      public IterEntry(Node<K, V> node, int index) {
        this.node = node;
        this.index = index;
      }
    }
  }
}
