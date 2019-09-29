package problems.indices.rankingtree.impl;

/**
 * Represents an entry in the ranked map where key is associated with certain value.
 */
class KeyValue<K, V> {
  private final K key;
  private V value;


  protected KeyValue(K key, V value) {
    this.key = key;
    this.value = value;
  }

  public static <K, V> KeyValue<K, V> of(K key, V value) {
    return new KeyValue<>(key, value);
  }

  public K getKey() {
    return key;
  }

  public V getValue() {
    return value;
  }

  public void setValue(V value) {
    this.value = value;
  }
}