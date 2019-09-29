package problems.indices.rankingtree.impl;

import java.util.*;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

import static java.util.Objects.requireNonNull;

/**
 * Work in progress: TODO: merge this with RankingTreeImpl
 *
 * Base class for ranking tree.
 *
 * This data structure offers the following traits:
 * <ul>
 *   <li>Fast insert operation</li>
 *   <li>Ability to find absolute position in the data set (offset, based on how key compares to the other keys)</li>
 * </ul>
 *
 * Top level capacity: n * w (n - cell capacity, w - number of nodes)
 * Each cell: [0..k..n]
 */
public final class RankingTree3<TKey extends Comparable<TKey>, TValue extends RankingTree3.Value<TKey>> {

  private static final int TRUNK_NODE_MAX_SIZE = 3;

  public static final class Rank<TKey extends Comparable<TKey>, TValue extends Value<TKey>> {
    private final TKey key;
    private final int rank;
    private final Node<TKey, TValue> node;

    public Rank(TKey key, int rank, Node<TKey, TValue> node) {
      this.key = requireNonNull(key);
      this.rank = rank;
      this.node = requireNonNull(node);
    }

    @Override
    public String toString() {
      return String.format("Rank{nodeId=%d, key=%s, rank=%d}", node.getId(), key, rank);
    }
  }

  public interface Value<TKey extends Comparable<TKey>> {
    TKey getKey();
  }

  public interface Node<TKey extends Comparable<TKey>, TValue extends Value<TKey>> {
    long getId();

    boolean isLeaf();

    default List<Rank<TKey, TValue>> getRanks() {
      throw new UnsupportedOperationException();
    }

    default Leaf<TKey, TValue> withValue(TValue value) {
      throw new UnsupportedOperationException();
    }

    default List<TValue> getValues() {
      throw new UnsupportedOperationException();
    }
  }

  public static abstract class Base<TKey extends Comparable<TKey>, TValue extends Value<TKey>> implements Node<TKey, TValue> {

    private static final AtomicLong NODE_ID_COUNTER = new AtomicLong();

    private final long id;

    Base() {
      this.id = NODE_ID_COUNTER.incrementAndGet();
    }

    @Override
    public long getId() {
      return id;
    }

    @Override
    public String toString() {
      final StringBuilder sb = new StringBuilder();
      if (isLeaf()) {
        sb.append("Leaf#").append(getValues());
      } else {
        sb.append("Trunk#").append(getRanks());
      }
      return sb.toString();
    }
  }

  public static final class Trunk<TKey extends Comparable<TKey>, TValue extends Value<TKey>> extends Base<TKey, TValue> {
    private final List<Rank<TKey, TValue>> ranks = new CopyOnWriteArrayList<>();

    @Override
    public boolean isLeaf() {
      return false;
    }

    @Override
    public List<Rank<TKey, TValue>> getRanks() {
      return ranks;
    }
  }

  public static final class Leaf<TKey extends Comparable<TKey>, TValue extends Value<TKey>> extends Base<TKey, TValue> {
    private final List<TValue> values;

    public Leaf() {
      this.values = Collections.emptyList();
    }

    Leaf(List<TValue> values) {
      this.values = values;
    }

    @Override
    public boolean isLeaf() {
      return true;
    }

    @Override
    public List<TValue> getValues() {
      return values;
    }

    @Override
    public Leaf<TKey, TValue> withValue(TValue value) {
      final List<TValue> v = new ArrayList<>(values.size() + 1);
      v.add(value);
      v.addAll(values);
      v.sort(Comparator.comparing(Value::getKey));
      return new Leaf<>(Collections.unmodifiableList(v));
    }
  }

  private final AtomicReference<Node<TKey, TValue>> root = new AtomicReference<>();

  public Optional<Rank<TKey, TValue>> tryInsert(TValue value) {
    Node<TKey, TValue> n = root.get();
    Rank<TKey, TValue> rank = insertRecursive(n, 0, value);
    if (root.compareAndSet(n, rank.node)) {
      return Optional.of(rank);
    }

    // algorithm: enqueue changes and modify the tree in one turn;
    // start with leaf nodes, insert all the values and go upwards.

    // (T+1) Ranking state:
    // 0: 1000, 1: 950, 2: 840, 3: 835, 4: 801, 5: 560, 6: 405, 7: 397
    // (T+2) Insert score=820
    // (T+3) Ranking state:
    // 0: 1000, 1: 950, 2: 840, 3: 835, 4: 820, 5: 801, 6: 560, 7: 405, 8: 397
    // Effective update for all scores starting with index 4.
    // Sample tree structure:
    //              0-8
    //            /  |  \
    //         0-3  3-6  6-8
    // Count of layers: log(N, K), where N is the number of elements and K - trunk node capacity
    // Complexity of insert operations (number of nodes that we'd need to touch):
    // Since we need to move element, keep leaf nodes unchanged (perhaps have a bg process that re-balances leaves),
    // we'd need to only update trunk node ranks.
    // Assuming M = K = 1000, and N = 1_000_000_000, we have three layers (last one is leaves);
    // 1st layer: 0-10^9
    // 2nd layer: 0-10^6, 10^6-2*10^6, ... 999*10^6-10^9
    // 3rd layer: 0-1000, 2000-3000, 3000-4000...
    // in total, we have 10^6 leaves and 1+10^3 trunk nodes.

    // can't set root due to conflict
    return Optional.empty();
  }

  private Rank<TKey, TValue> insertRecursive(Node<TKey, TValue> n, int startRank, TValue value) {
    if (n.isLeaf()) {
      int index = Collections.binarySearch(n.getValues(), value, Comparator.comparing(Value::getKey));
      if (index < 0) {
        index = -index - 1;
      }

      final List<TValue> values = new ArrayList<>(n.getValues().size() + 1);
      values.addAll(n.getValues().subList(0, index));
      values.add(value);
      values.addAll(n.getValues().subList(index, n.getValues().size()));
      final Node<TKey, TValue> node = new Leaf<>(values);
      return new Rank<>(value.getKey(), startRank + index, node);
    } else {
      throw new UnsupportedOperationException();
    }
  }
}
