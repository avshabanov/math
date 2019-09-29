package problems.indices.rankingtree.impl;

import problems.indices.rankingtree.RankedResult;
import problems.indices.rankingtree.RankingTree;

import java.util.Objects;

/**
 * Ranking tree implementation based on B+ tree.
 *
 * TODO: add re-balancing code
 * TODO: add grow capacity code
 */
public final class RankingBPlusTree<K extends Comparable<K>, V> implements RankingTree<K, V> {

  private final BNode.Branch<K> root = new BNode.Branch<>();

  //
  // Public
  //


  @Override
  public int size() {
    return this.root.getSize();
  }

  /**
   * Puts key-value pair into the tree.
   *
   * Algorithm: enqueue changes and modify the tree in one turn;
   * start with leaf nodes, insert all the values and go upwards.
   *
   * (T+1) Ranking state:
   * 0: 1000, 1: 950, 2: 840, 3: 835, 4: 801, 5: 560, 6: 405, 7: 397
   * (T+2) Insert score=820
   * (T+3) Ranking state:
   * 0: 1000, 1: 950, 2: 840, 3: 835, 4: 820, 5: 801, 6: 560, 7: 405, 8: 397
   * Effective update for all scores starting with index 4.
   * Sample tree structure:
   *              0-8
   *            /  |  \
   *         0-3  3-6  6-8
   * Count of layers: log(N, K), where N is the number of elements and K - trunk node capacity
   * Complexity of insert operations (number of nodes that we'd need to touch):
   * Since we need to move element, keep leaf nodes unchanged (perhaps have a bg process that re-balances leaves),
   * we'd need to only update trunk node ranks.
   * Assuming M = K = 1000, and N = 1_000_000_000, we have three layers (last one is leaves);
   * 1st layer: 0-10^9
   * 2nd layer: 0-10^6, 10^6-2*10^6, ... 999*10^6-10^9
   * 3rd layer: 0-1000, 2000-3000, 3000-4000...
   * in total, we have 10^6 leaves and 1+10^3 trunk nodes.
   *
   * @param key Key, can't be null
   * @param value Value, can't be null
   * @return Ranking result
   */
  @Override
  public RankedResult<V> put(K key, V value) {
    Objects.requireNonNull(key, "key");
    Objects.requireNonNull(value, "value");

    // use existing tree structure, grow whatever leaf array we find matching the criteria
    int offset = 0;
    for (BNode.Branch<K> n = root;;) {
      for (int i = 0; i < n.getPointerCapacity(); ++i) {
        final Pointer<K> ptr = n.getPointer(i);
        if (ptr == null) {
          // pointer is uninitialized, we can insert our key right here
          final BNode.Leaf<K, V> leaf = new BNode.Leaf<>();
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
          final BNode<K> childBNode = ptr.BNode;
          if (childBNode.isLeaf()) {
            // search within the leaf
            final BNode.Leaf<K, V> leaf = (BNode.Leaf<K, V>) childBNode;
            final RankedResult<V> result = leaf.put(offset, key, value);
            if (result.getValue() == null) {
              // value has been inserted, so pointer size needs to be updated
              // TODO: update size of all the upstream nodes too
              ptr.size = ptr.size + 1;
            }

            return result;
          } else {
            // walk down a branch node
            n = (BNode.Branch<K>) childBNode;
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
    for (BNode.Branch<K> n = root; n.getPointerCount() > 0;) {
       for (int i = 0; i < n.getPointerCount(); ++i) {
        final Pointer<K> ptr = n.getPointer(i);
        final Pointer<K> nextPtr = (i + 1) < n.getPointerCount() ? n.getPointer(i + 1) : null;
        final K nextKey = nextPtr != null ? nextPtr.startKey : null;
        int rhsCompare = nextKey != null ? key.compareTo(nextKey) : -1;
        if (rhsCompare < 0) {
          // we found the pointer, proceed to downstream node
          final BNode<K> childBNode = ptr.BNode;
          if (childBNode.isLeaf()) {
            // search within the leaf
            final BNode.Leaf<K, V> leaf = (BNode.Leaf<K, V>) childBNode;
            return leaf.get(offset, key);
          } else {
            n = (BNode.Branch<K>) childBNode;
            continue;
          }
        }

        // we'd need to continue the search
        offset += ptr.size;
      }
    }

    return null;
  }

  @Override
  public RankedResult<V> delete(K key) {
    throw new UnsupportedOperationException();
  }
}
