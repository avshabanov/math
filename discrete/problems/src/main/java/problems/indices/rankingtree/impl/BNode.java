package problems.indices.rankingtree.impl;

import problems.indices.rankingtree.RankedResult;

import java.util.Arrays;
import java.util.Comparator;

/**
 * Represents a pointer to certain section of a B+ tree.
 * There are two kinds of B+ tree nodes: branches and leaves.
 */
interface BNode<K extends Comparable<K>> {

  /** Max capacity of a the pointer node. */
  int POINTER_CAPACITY = 4;

  /** Max capacity of a the leaf node node. */
  int LEAF_CAPACITY = 4;

  default boolean isLeaf() {
    return false;
  }

  K getFirstKey();
  int getSize();

  final class Branch<K extends Comparable<K>> implements BNode<K> {
    @SuppressWarnings("unchecked")
    private Pointer<K>[] pointers = new Pointer[POINTER_CAPACITY];
    private int pointerCount;

    @Override
    public K getFirstKey() {
      if (this.pointerCount == 0) {
        throw new IllegalStateException("Key is unavailable as branch has not yet been initialized");
      }
      final Pointer<K> pointer = this.pointers[0];
      if (pointer == null) {
        throw new IllegalStateException("Invariant failure: first point should be initialized but it is not");
      }
      return pointer.startKey;
    }

    @Override
    public int getSize() {
      int result = 0;
      for (int i = 0; i < this.pointerCount; ++i) {
        result += this.pointers[i].size;
      }
      return result;
    }

    Pointer<K> getPointer(int pos) {
      if (pos < 0 || pos >= pointers.length) {
        throw new IllegalArgumentException("pos=" + pos);
      }
      return this.pointers[pos];
    }

    int getPointerCapacity() {
      return this.pointers.length;
    }

    int getPointerCount() {
      return this.pointerCount;
    }

    void addPointer(BNode<K> downstream) {
      if (this.pointerCount >= POINTER_CAPACITY) {
        throw new UnsupportedOperationException("Oversize capacity");
      }

      final int pos = this.pointerCount;
      this.pointerCount = this.pointerCount + 1;

      if (this.pointers[pos] != null) {
        throw new IllegalStateException("Can't initialize pointer which has been initialized before; pos=" + pos);
      }

      final Pointer<K> pointer = new Pointer<>();
      pointer.startKey = downstream.getFirstKey();
      pointer.size = downstream.getSize();
      pointer.BNode = downstream;
      this.pointers[pos] = pointer;
    }
  }

  final class Leaf<K extends Comparable<K>, V> implements BNode<K> {
    @SuppressWarnings("unchecked")
    private KeyValue<K, V>[] values = new KeyValue[LEAF_CAPACITY];
    private int size;
    private Leaf<K, V> next;

    @Override
    public boolean isLeaf() {
      return true;
    }

    @Override
    public K getFirstKey() {
      if (this.size == 0) {
        throw new IllegalArgumentException("Empty leaf node");
      }
      return this.values[0].getKey();
    }

    @Override
    public int getSize() {
      return this.size;
    }

    RankedResult<V> put(int offset, K key, V value) {
      int pos = search(key);
      if (pos >= 0) {
        // override existing value
        final KeyValue<K, V> current = this.values[pos];
        final V previousValue = current.getValue();
        current.setValue(value);
        return RankedResult.of(offset + pos, previousValue);
      }

      // add new value
      if (this.size >= LEAF_CAPACITY) {
        throw new UnsupportedOperationException("Oversize capacity");
      }

      pos = -pos - 1;
      KeyValue<K, V> current = KeyValue.of(key, value);
      KeyValue<K, V> previous = this.values[pos];
      this.values[pos] = current;

      // move remainder of elements forward
      for (int p = pos + 1; p < this.size; ++p) {
        current = this.values[p];
        this.values[p] = previous;
        previous = current;
      }

      this.size = this.size + 1;
      return RankedResult.of(offset + pos, null);
    }

    RankedResult<V> get(int offset, K key) {
      int pos = search(key);
      if (pos < 0) {
        return null;
      }

      return RankedResult.of(offset + pos, this.values[pos].getValue());
    }

    private int search(K key) {
      final KeyValue<K, V> adaptedKey = KeyValue.of(key, null);
      return Arrays.binarySearch(this.values, 0, this.size, adaptedKey, Comparator.comparing(KeyValue::getKey));
    }
  }
}

final class Pointer<K extends Comparable<K>> {
  K startKey;
  BNode<K> BNode;
  // total count of items corresponding to this node
  int size;
}
