package problems.indices.rankingtree;

/**
 * Ranking map is a map-alike data structure that supports dense ordering (ranking) for its elements based upon
 * comparison operation, so that the smallest element has ranking of 0, element next to smallest is ranked 1,
 * then 2 and so forth.
 */
public interface RankingTree<K extends Comparable<K>, V> {

  RankedResult<V> get(K key);

  RankedResult<V> put(K key, V value);

  RankedResult<V> delete(K key);

  int size();
}
