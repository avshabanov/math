package problems.indices.rankingtree;

/**
 * Ranking map is a map-alike data structure that supports dense ordering (ranking) for its elements based upon
 * comparison operation, so that the greatest element has ranking of 0, next one is ranked 1, then 2 and so forth.
 */
public interface RankingTree<K extends Comparable<K>, V> {

  RankedResult<V> get(K key);

  RankedResult<V> put(K key, V value);

  RankedResult<V> delete(K key);

  int size();
}
