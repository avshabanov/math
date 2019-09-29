package problems.indices.rankingtree.impl;

import problems.indices.rankingtree.RankedResult;
import problems.indices.rankingtree.RankingTree;

import java.util.Objects;

/**
 * Ranking tree implementation.
 */
public final class RankingTreeImpl<K extends Comparable<K>, V> implements RankingTree<K, V> {

  private final Node.Branch<K> root = new Node.Branch<>();

  //
  // Public
  //


  @Override
  public int size() {
    return this.root.getSize();
  }

  @Override
  public RankedResult<V> put(K key, V value) {
    Objects.requireNonNull(key, "key");
    Objects.requireNonNull(value, "value");

    // use existing tree structure, grow whatever leaf array we find matching the criteria
    int offset = 0;
    for (Node.Branch<K> n = root;;) {
      for (int i = 0; i < n.getPointerCapacity(); ++i) {
        final Pointer<K> ptr = n.getPointer(i);
        if (ptr == null) {
          // pointer is uninitialized, we can insert our key right here
          final Node.Leaf<K, V> leaf = new Node.Leaf<>();
          final RankedResult<V> result = leaf.put(offset, key, value);
          n.addPointer(leaf);
          return result;
        }

        // pointer has been found, check if it is the right candidate for insertion
        final Pointer<K> nextPtr = (i + 1) < n.getPointerCount() ? n.getPointer(i + 1) : null;
        final K nextKey = nextPtr != null ? nextPtr.startKey : null;
        final int rhsCompare = nextKey != null ? key.compareTo(nextKey) : -1;
        if (rhsCompare < 0) {
          // we found the pointer, proceed to the downstream node
          final Node<K> childNode = ptr.node;
          if (childNode.isLeaf()) {
            // search within the leaf
            final Node.Leaf<K, V> leaf = (Node.Leaf<K, V>) childNode;
            final RankedResult<V> result = leaf.put(offset, key, value);
            if (result.getValue() == null) {
              // value has been inserted, so pointer size needs to be updated
              // TODO: update size of all the upstream nodes too
              ptr.size = ptr.size + 1;
            }

            return result;
          } else {
            // walk down a branch node
            n = (Node.Branch<K>) childNode;
            continue;
          }
        }

        // we'd need to continue the search
        offset += ptr.size;
      }
    }
  }

  @Override
  public RankedResult<V> get(K key) {
    int offset = 0;
    for (Node.Branch<K> n = root; n.getPointerCount() > 0;) {
       for (int i = 0; i < n.getPointerCount(); ++i) {
        final Pointer<K> ptr = n.getPointer(i);
        final Pointer<K> nextPtr = (i + 1) < n.getPointerCount() ? n.getPointer(i + 1) : null;
        final K nextKey = nextPtr != null ? nextPtr.startKey : null;
        int rhsCompare = nextKey != null ? key.compareTo(nextKey) : -1;
        if (rhsCompare < 0) {
          // we found the pointer, proceed to downstream node
          final Node<K> childNode = ptr.node;
          if (childNode.isLeaf()) {
            // search within the leaf
            final Node.Leaf<K, V> leaf = (Node.Leaf<K, V>) childNode;
            return leaf.get(offset, key);
          } else {
            n = (Node.Branch<K>) childNode;
            continue;
          }
        }

        // we'd need to continue the search
        offset += ptr.size;
      }
    }

    return null;
  }
}
