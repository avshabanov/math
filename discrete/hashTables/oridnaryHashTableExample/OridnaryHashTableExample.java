import java.util.*;

/**
 * @author Alexander Shabanov
 */
public class OridnaryHashTableExample {

  public static void main(String[] args) {
    final Map<Integer, String> map = new SimpleHashTable<>();
    map.put(1, "one");
    map.put(2, "two");
    map.put(3, "three");
    map.put(4, "four");
    map.put(5, "five");
    map.put(6, "six");
    map.put(7, "seven");
    map.put(8, "eight");
    System.out.println("map=" + map);
    map.remove(2);
    System.out.println("map=" + map);
    map.put(3, "tres");
    System.out.println("map=" + map);
  }

  public static final class SimpleHashTable<K, V> extends AbstractMap<K, V> implements Map<K, V> {
    public static final int DEFAULT_INITIAL_CAPACITY = 4;
    public static final float DEFAULT_LOAD_FACTOR = 0.75f;
    public static final int MAX_CAPACITY = 1 << 30;

    private EntryImpl<K, V> arr[];
    private int size;
    private final float loadFactor;

    public SimpleHashTable(int initialCapacity, float loadFactor) {
      if (initialCapacity < 0 || initialCapacity > MAX_CAPACITY) {
        throw new IllegalArgumentException("initialCapacity");
      }

      if (loadFactor <= 0.0f || loadFactor > 1.0f) {
        throw new IllegalArgumentException("loadFactor");
      }

      this.loadFactor = loadFactor;
      this.arr = newEntries(initialCapacity);
    }

    public SimpleHashTable() {
      this(DEFAULT_INITIAL_CAPACITY, DEFAULT_LOAD_FACTOR);
    }

    @SuppressWarnings("NullableProblems")
    @Override
    public Set<Entry<K, V>> entrySet() {
      // inefficient entry transform
      final Set<Entry<K, V>> result = new HashSet<>(size() * 2);

      //noinspection ForLoopReplaceableByForEach
      for (int i = 0; i < arr.length; ++i) {
        for (EntryImpl<K, V> it = arr[i]; it != null; it = it.next) {
          result.add(it);
        }
      }

      return result;
    }

    @Override
    public V get(Object key) {
      for (EntryImpl<K, V> entry = arr[getPosFromHashCode(key)]; entry != null; entry = entry.next) {
        if (Objects.equals(entry.key, key)) {
          return entry.value;
        }
      }

      return null;
    }

    @Override
    public V put(K key, V value) {
      int pos = getPosFromHashCode(key);
      final EntryImpl<K, V> entry = arr[pos];
      for (EntryImpl<K, V> it = entry; it != null; it = it.next) {
        if (Objects.equals(it.key, key)) {
          // found existing entry
          final V old = it.value;
          it.value = value;
          return old;
        }
      }

      resizeIfNeeded();

      final EntryImpl<K, V> e = new EntryImpl<>(key, value);
      e.next = entry;
      if (entry != null) {
        entry.prev = e;
      }
      arr[pos] = e;
      ++size;

      return null;
    }

    @Override
    public V remove(Object key) {
      int pos = getPosFromHashCode(key);
      final EntryImpl<K, V> entry = arr[pos];
      for (EntryImpl<K, V> it = entry; it != null; it = it.next) {
        if (Objects.equals(it.key, key)) {
          // found existing entry
          final V old = it.value;

          // adjust the links
          if (it.next != null) {
            it.next.prev = it.prev;
          }
          if (it.prev != null) {
            it.prev.next = it.next;
          }

          return old;
        }
      }

      return null; // no such value
    }

    @Override
    public int size() {
      return size;
    }

    //
    // Private
    //

    private void resizeIfNeeded() {
      // TODO: implement
    }

    private int getPosFromHashCode(Object key) {
      int result = Objects.hashCode(key);
      result = result % arr.length;
      if (result < 0) {
        result = -result;
      }
      return result;
    }

    private static <K, V> EntryImpl<K, V>[] newEntries(int size) {
      @SuppressWarnings("unchecked") final EntryImpl<K, V>[] arr = new EntryImpl[size];
      return arr;
    }

    @SuppressWarnings("NullableProblems")
    private static final class EntryImpl<K, V> implements Entry<K, V> {
      final K key;
      V value;
      EntryImpl<K, V> prev;
      EntryImpl<K, V> next;

      public EntryImpl(K key, V value) {
        this.key = key;
        this.value = value;
      }

      @Override
      public K getKey() {
        return key;
      }

      @Override
      public V getValue() {
        return value;
      }

      @Override
      public V setValue(V value) {
        final V old = this.value;
        this.value = value;
        return old;
      }

      @Override
      public int hashCode() {
        return Objects.hashCode(key);
      }

      @SuppressWarnings("EqualsWhichDoesntCheckParameterClass")
      @Override
      public boolean equals(Object other) {
        return Objects.equals(key, other);
      }

      @Override
      public String toString() {
        return "{key=" + key + ", value=" + value + '}';
      }
    }
  }
}
