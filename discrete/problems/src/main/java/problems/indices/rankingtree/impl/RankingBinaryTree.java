package problems.indices.rankingtree.impl;

import problems.indices.rankingtree.RankedResult;
import problems.indices.rankingtree.RankingTree;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * Ranking tree based upon binary search tree without balancing code.
 */
public class RankingBinaryTree<K extends Comparable<K>, V> implements RankingTree<K, V> {

  private static final class Node<K, V> extends KeyValue<K, V> {
    private int sizeOfLeftSubtree;
    private Node<K, V> left;
    private Node<K, V> right;

    Node(K key, V value) {
      super(key, value);
    }

    HolderOfNodePointer<K, V> getLeftHolder() {
      return (n) -> this.left = n;
    }

    HolderOfNodePointer<K, V> getRightHolder() {
      return (n) -> this.right = n;
    }

    // pretty printing for debug purposes only
    @Override
    public String toString() {
      final StringBuilder sb = new StringBuilder(100);
      appendNode(sb, 0, this);
      return sb.toString();
    }

    private static <K, V> void appendNode(StringBuilder sb, int printOffset, Node<K, V> n) {
      if (n == null) {
        return;
      }

      appendNode(sb, printOffset + 1, n.left);
      for (int i = 0; i < printOffset; ++i) {
        sb.append(' ');
      }
      sb.append(String.format("%s: %s (left subtree size: %d)\n", n.getKey(), n.getValue(), n.sizeOfLeftSubtree));
      appendNode(sb, printOffset + 1, n.right);
    }
  }

  private interface HolderOfNodePointer<K, V> {
    void set(Node<K, V> n);
  }

  private HolderOfNodePointer<K, V> getRootHolder() {
    return (n) -> this.root = n;
  }

  private Node<K, V> root;

  //
  // Public
  //

  @Override
  public RankedResult<V> get(K key) {
    Objects.requireNonNull(key, "key");

    int offset = 0;
    for (Node<K, V> n = root; n != null;) {
      final int cmp = key.compareTo(n.getKey());
      if (cmp == 0) {
        return RankedResult.of(n.sizeOfLeftSubtree + offset, n.getValue());
      }

      if (cmp > 0) {
        offset = offset + n.sizeOfLeftSubtree + 1;
        n = n.right;
      } else {
        n = n.left;
      }
    }

    return null;
  }

  @Override
  public RankedResult<V> put(K key, V value) {
    Objects.requireNonNull(key, "key");
    Objects.requireNonNull(key, "value");

    int offset = 0;
    HolderOfNodePointer<K, V> h = getRootHolder();
    List<Node<K, V>> parentsToTheRight = new ArrayList<>();
    for (Node<K, V> n = root; n != null;) {
      final int cmp = key.compareTo(n.getKey());
      if (cmp == 0) {
        // override scenario
        final V oldValue = n.getValue();
        n.setValue(value);
        return RankedResult.of(n.sizeOfLeftSubtree + offset, oldValue);
      }

      if (cmp > 0) {
        offset = offset + n.sizeOfLeftSubtree + 1;
        h = n.getRightHolder();
        n = n.right;
      } else {
        h = n.getLeftHolder();
        parentsToTheRight.add(n);
        n = n.left;
      }
    }

    // associate referrer (root or left or right node pointer) with the new node
    h.set(new Node<>(key, value));

    // increment size of all parents right to this node
    for (final Node<K, V> parentToTheRight : parentsToTheRight) {
      ++parentToTheRight.sizeOfLeftSubtree;
    }

    return RankedResult.of(offset, null);
  }

  @Override
  public RankedResult<V> delete(K key) {
    Objects.requireNonNull(key, "key");

    RankedResult<V> result = null;
    int offset = 0;
    HolderOfNodePointer<K, V> h = getRootHolder();
    List<Node<K, V>> parentsToTheRight = new ArrayList<>();
    Node<K, V> n = root;
    while (n != null) {
      final int cmp = key.compareTo(n.getKey());
      if (cmp == 0) {
        // found node to be deleted
        result = RankedResult.of(n.sizeOfLeftSubtree + offset, n.getValue());
        break;
      }

      if (cmp > 0) {
        offset = offset + n.sizeOfLeftSubtree + 1;
        h = n.getRightHolder();
        n = n.right;
      } else {
        h = n.getLeftHolder();
        parentsToTheRight.add(n);
        n = n.left;
      }
    }

    if (result == null) {
      return null; // nothing found
    }


    if (n.left == null) {
      // simple case: there is no left subtree => swapping with right node should cover all the cases
      h.set(n.right);
    } else {
      // we need to swap the node that we need to remove with the rightmost node of its left subtree
      // and account for the case which is the consequence of not balancing this tree: degenerate case when
      // subtree is a linked-list alike structure
      Node<K, V> candidate = n.left;
      HolderOfNodePointer<K, V> innerHolder = h;
      while (candidate.right != null) {
        innerHolder = candidate.getRightHolder();
        candidate = candidate.right;
      }

      innerHolder.set(candidate.left);

      if (candidate != n.left) {
        candidate.left = n.left;
      } else {
        // special case: degenerate left subtree
        candidate.left = n.left.left;
      }

      candidate.right = n.right;
      candidate.sizeOfLeftSubtree = n.sizeOfLeftSubtree - 1;
      h.set(candidate);
    }

    for (Node<K, V> p : parentsToTheRight) {
      p.sizeOfLeftSubtree--;
    }

    return result;
  }

  @Override
  public int size() {
    int result = 0;
    for (Node<K, V> n = root; n != null; n = n.right) {
      result = result + n.sizeOfLeftSubtree + 1;
    }
    return result;
  }
}
