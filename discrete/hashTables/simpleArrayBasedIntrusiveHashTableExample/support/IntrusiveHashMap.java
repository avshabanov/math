package support;

import java.util.Collection;

/**
 * Simple intrusive hash table. Intrusiveness implies that a key is always a part of a value.
 * This interface should work only with non-null keys and values.
 *
 * @param <K> Key type
 * @param <V> Value type
 *
 * @author Alexander Shabanov
 */
public interface IntrusiveHashMap<K, V> extends Collection<V> {

  V putValue(V value);

  V getByKey(K key);

  default boolean containsKey(K key) {
    return getByKey(key) == null;
  }
}
