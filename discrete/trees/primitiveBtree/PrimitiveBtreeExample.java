import java.util.*;

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
 */
public final class PrimitiveBtreeExample {

  public static void main(String[] args) {
    demo1();
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

  // TODO: complete (balancing, removal, iteration)

  private static final class Btree<K extends Comparable<K>, V> {
    private Node<K, V> root;
    private final int nodeSize;

    public Btree(int nodeSize) {
      this.nodeSize = nodeSize;
    }

    public V put(K key, V value) {
      if (root == null) {
        this.root = newNode(key, value);
        return null;
      }

      for (Node<K, V> n = root;;) {
        final List<? extends Comparable<? super K>> keys = n;
        int index = Collections.binarySearch(keys, key);

        // found existing value
        if (index >= 0) {
          final KeyValue<K, V> kv = n.keyValues[index];
          final V prevValue = kv.value;
          kv.value = value;
          return prevValue;
        }

        index = -1 - index;
        if (n.size < nodeSize) {
          final int nextIndex = index + 1;
          final int rangeSize = n.size - index;
          if (rangeSize > 0) {
            System.arraycopy(n.keyValues, index, n.keyValues, nextIndex, n.size - nextIndex);
            System.arraycopy(n.children, index, n.children, nextIndex, n.size - nextIndex);
          }
          ++n.size;
          n.keyValues[index] = new KeyValue<>(key, value);
          n.children[index] = null; // reset child pointer

          return null; // new value inserted
        }

        // node capacity is full - need to insert a new one
        final Node<K, V> childNode = n.children[index];
        if (childNode == null) {
          // insert child node with a single value
          n.children[index] = newNode(key, value);
          return null;
        }

        n = childNode;
      }
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
      return node;
    }
  }

  private static final class KeyValue<K extends Comparable<K>, V> implements Comparable<KeyValue<K, V>> {
    final K key;
    V value;

    public KeyValue(K key, V value) {
      this.key = key;
      this.value = value;
    }


    @SuppressWarnings("NullableProblems")
    @Override
    public int compareTo(KeyValue<K, V> other) {
      return key.compareTo(other.key);
    }
  }


  // implements List to make binary search simpler
  private static final class Node<K extends Comparable<K>, V>
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
}
