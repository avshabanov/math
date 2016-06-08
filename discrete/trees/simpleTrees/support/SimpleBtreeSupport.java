package support;

import java.util.*;
import java.util.function.Supplier;

/**
 * @author Alexander Shabanov
 */
public abstract class SimpleBtreeSupport {

  protected static final class RandomShuffleResult<B extends Btree<Integer, String>> {
    private final B btree;
    private final List<KeyValue<Integer, String>> pairs;

    public RandomShuffleResult(B btree, List<KeyValue<Integer, String>> pairs) {
      this.btree = btree;
      this.pairs = pairs;
    }

    public B getBtree() {
      return btree;
    }

    public List<KeyValue<Integer, String>> getPairs() {
      return pairs;
    }
  }

  protected static <B extends Btree<Integer, String>> RandomShuffleResult<B> createRandomShuffleBtree(
      int size,
      Supplier<B> btreeSupplier) {
    // initialize shuffled values
    final List<KeyValue<Integer, String>> pairs = new ArrayList<>(size);
    for (int i = 0; i < size; ++i) {
      pairs.add(new KeyValue<>(i, "#" + i));
    }
    final Random random = new Random(3546587416845138457L);
    for (int i = 0; i < 10 * size; ++i) {
      Collections.swap(pairs, i % size, random.nextInt(size));
    }

    // add values
    final B btree = btreeSupplier.get();
    final BtreeStatistics statistics = new SimpleBtreeStatistics();
    btree.setStatistics(statistics);
    for (final KeyValue<Integer, String> kv : pairs) {
      final String v = btree.put(kv.getKey(), kv.getValue());
      if (v != null) {
        throw new AssertionError("prev value is not null");
      }
    }

    return new RandomShuffleResult<>(btree, pairs);
  }

  // TODO: complete (balancing, removal, iteration)

  protected static class Btree<K extends Comparable<K>, V> {
    protected Node<K, V> root;
    protected final int nodeSize;

    protected BtreeStatistics statistics = BtreeStatistics.EMPTY;

    public Btree(int nodeSize) {
      this.nodeSize = nodeSize;
    }

    public Node<K, V> getRoot() {
      return root;
    }

    public int getNodeSize() {
      return nodeSize;
    }

    public BtreeStatistics getStatistics() {
      return statistics;
    }

    public void setStatistics(BtreeStatistics statistics) {
      this.statistics = statistics;
    }

    public V put(K key, V value) {
      if (root == null) {
        this.root = newNode(key, value);
        return null;
      }

      V result = null;
      int depth = 0;
      for (Node<K, V> n = root;; ++depth) {
        final List<? extends Comparable<? super K>> keys = n;
        int index = Collections.binarySearch(keys, key);

        // found existing value
        if (index >= 0) {
          final KeyValue<K, V> kv = n.keyValues[index];
          result = kv.value;
          kv.value = value;
          break;
        }

        index = -1 - index;
        if (n.size < nodeSize) {
          final int nextIndex = index + 1;
          final int rangeSize = n.size - index;
          if (rangeSize > 0) {
            System.arraycopy(n.keyValues, index, n.keyValues, nextIndex, rangeSize);
            System.arraycopy(n.children, index, n.children, nextIndex, rangeSize);
          }
          ++n.size;
          n.keyValues[index] = new KeyValue<>(key, value);
          n.children[index] = null; // reset child pointer
          break;
        }

        // node capacity is full - need to insert a new one
        final Node<K, V> childNode = n.children[index];
        if (childNode == null) {
          // insert child node with a single value
          n.children[index] = newNode(key, value);
          break;
        }

        n = childNode;
      }

      statistics.putDepth(depth);
      return result;
    }

    public V get(K key) {
      for (Node<K, V> n = root; n != null;) {
        final List<? extends Comparable<? super K>> keys = n;
        int index = Collections.binarySearch(keys, key);

        // found existing value
        if (index >= 0) {
          return n.keyValues[index].value;
        }

        index = -1 - index;
        n = n.children[index];
      }

      return null;
    }

    private Node<K, V> newNode(K key, V value) {
      final Node<K, V> node = new Node<>(nodeSize);
      node.keyValues[0] = new KeyValue<>(key, value);
      node.size = 1;
      statistics.nodeCreated();
      return node;
    }
  }

  protected static final class KeyValue<K extends Comparable<K>, V> implements Comparable<KeyValue<K, V>> {
    final K key;
    V value;

    public KeyValue(K key, V value) {
      this.key = key;
      this.value = value;
    }

    public K getKey() {
      return key;
    }

    public V getValue() {
      return value;
    }

    @SuppressWarnings("NullableProblems")
    @Override
    public int compareTo(KeyValue<K, V> other) {
      return key.compareTo(other.key);
    }

    @Override
    public String toString() {
      return "{" + getKey() + ": " + getValue() + '}';
    }
  }


  // implements List to make binary search simpler
  protected static final class Node<K extends Comparable<K>, V>
      extends AbstractList<K>
      implements RandomAccess {

    private final KeyValue<K, V> keyValues[];
    private final Node<K, V> children[];
    private int size;

    @SuppressWarnings("unchecked")
    public Node(int order) {
      this.keyValues = new KeyValue[order];
      this.children = new Node[order + 1];
    }

    public KeyValue<K, V>[] getKeyValues() {
      return keyValues;
    }

    public Node<K, V>[] getChildren() {
      return children;
    }

    public int getSize() {
      return size;
    }

    @Override
    public K get(int index) {
      final KeyValue<K, V> kv = keyValues[index];
      if (kv == null) {
        throw new IllegalStateException("Internal error: keyValue is null for index=" + index);
      }

      return kv.key;
    }

    @Override
    public int size() {
      return size;
    }
  }

  // statistics

  protected interface BtreeStatistics {
    BtreeStatistics EMPTY = new BtreeStatistics() {
      @Override public void nodeCreated() { /* do nothing */ }
      @Override public void putDepth(int depth) { /* do nothing */ }
    };

    void nodeCreated();

    void putDepth(int depth);
  }

  protected static final class SimpleBtreeStatistics implements BtreeStatistics {
    private int nodesCreated;
    private int maxPutDepth;

    public SimpleBtreeStatistics() {
      nodesCreated = 0;
      maxPutDepth = 0;
    }

    @Override
    public void nodeCreated() {
      ++nodesCreated;
    }

    @Override
    public void putDepth(int depth) {
      maxPutDepth = Math.max(maxPutDepth, depth);
    }

    @Override
    public String toString() {
      return "{nodesCreated=" + nodesCreated +
          ", maxPutDepth=" + maxPutDepth +
          '}';
    }
  }
}
