package support;

import java.util.*;
import java.util.function.Function;

/**
 * Implementation of intrusive hash table based on single array. Good for small table sizes and works great
 * for reading-intensive scenarios.
 *
 * Space efficiency reached at the cost of remove operations which can be very slow - O(n).
 *
 * @param <K> Key type
 * @param <V> Value type
 *
 * @author Alexander Shabanov
 */
public abstract class SimpleIntrusiveHashTable<K, V> extends AbstractCollection<V>
    implements IntrusiveHashTable<K, V> {
  public static final int DEFAULT_INITIAL_CAPACITY = 4;
  public static final float DEFAULT_LOAD_FACTOR = 0.75f;
  public static final int MAX_CAPACITY = 1 << 30;

  private int size;
  private Object[] values; // all the values are of type V
  private final float loadFactor;

  // Factory methods

  public static <E> IntrusiveHashTable<E, E> createSet(int initialCapacity, float loadFactor) {
    return new InternalSet<>(initialCapacity, loadFactor);
  }

  public static <E> IntrusiveHashTable<E, E> createSet(int initialCapacity) {
    return createSet(initialCapacity, DEFAULT_LOAD_FACTOR);
  }

  public static <E> IntrusiveHashTable<E, E> createSet() {
    return createSet(DEFAULT_INITIAL_CAPACITY);
  }

  public static <K, V> IntrusiveHashTable<K, V> createMap(int initialCapacity,
                                                          float loadFactor,
                                                          Function<V, K> keyExtractor) {
    return new InternalMap<>(initialCapacity, loadFactor, keyExtractor);
  }

  public static <K, V> IntrusiveHashTable<K, V> createMap(int initialCapacity, Function<V, K> keyExtractor) {
    return createMap(initialCapacity, DEFAULT_LOAD_FACTOR, keyExtractor);
  }

  public static <K, V> IntrusiveHashTable<K, V> createMap(Function<V, K> keyExtractor) {
    return createMap(DEFAULT_INITIAL_CAPACITY, keyExtractor);
  }

  protected SimpleIntrusiveHashTable(int initialCapacity, float loadFactor) {
    this.loadFactor = loadFactor;

    if (initialCapacity < 0) {
      throw new IllegalArgumentException("initialCapacity can't be negative");
    }

    if (initialCapacity > MAX_CAPACITY) {
      throw new IllegalArgumentException("initialCapacity is too big");
    }

    if (loadFactor <= 0.0f || loadFactor >= 1.0f) {
      throw new IllegalArgumentException("loadFactor should be strictly between zero and one");
    }

    this.values = new Object[initialCapacity];
  }

  @SuppressWarnings("NullableProblems")
  @Override
  public Iterator<V> iterator() {
    return new Iter<>(this);
  }

  @Override
  public int size() {
    return size;
  }

  @Override
  public boolean add(V v) {
    putValue(v);
    return true;
  }

  @Override
  public void clear() {
    Arrays.fill(values, null);
    size = 0;
  }

  // O(n) complexity
  @Override
  public boolean remove(Object valueToRemove) {
    // TODO: don't use casts like this
    @SuppressWarnings("unchecked") final V value = (V) valueToRemove;
    final K key = getKeyFromValue(value);

    final int hashCode = key.hashCode();
    int removeIndex = -1;
    for (int pos = getPositiveHashCode(hashCode, values.length), count = 0; count < values.length; ++count) {
      @SuppressWarnings("unchecked") final V objValue = (V) values[pos];
      if (objValue == null) {
        break; // no such value
      }

      final K otherKey = getKeyFromValue(objValue);
      if (otherKey.hashCode() == hashCode && otherKey.equals(key)) {
        removeIndex = pos;
        break;
      }
    }

    if (removeIndex < 0) {
      return false;
    }

    removeElementAtIndex(removeIndex);

    return true;
  }

  // O(1) amortized complexity, O(n) - worst case
  @Override
  public V putValue(V value) {
    if (value == null) {
      throw new IllegalArgumentException("value can't be null");
    }

    resizeIfNeeded();

    // insert value
    final K key = getKeyFromValue(value);
    final int hashCode = key.hashCode();

    V otherValue = null;
    int foundPos = -1;

    for (int pos = getPositiveHashCode(hashCode, values.length), count = 0; count < values.length; ++count) {
      @SuppressWarnings("unchecked") final V objValue = (V) values[pos];
      if (objValue == null) {
        otherValue = null;
        foundPos = pos;
        break;
      }

      // value is not null - try to match it against the key
      final K otherKey = getKeyFromValue(objValue);
      if (otherKey.hashCode() == hashCode && otherKey.equals(key)) {
        otherValue = objValue;
        foundPos = pos;
        break;
      }

      // go to next pos - this value does not match
      ++pos;
    }

    if (foundPos < 0) {
      throw new IllegalStateException("Hashtable overflow"); // should not happen
    }

    values[foundPos] = value;
    ++size;
    return otherValue;
  }

  // O(1) amortized complexity, O(n) - worst case
  @Override
  public V getByKey(K key) {
    final int hashCode = key.hashCode();
    for (int pos = getPositiveHashCode(hashCode, values.length), count = 0; count < values.length; ++count) {
      @SuppressWarnings("unchecked") final V objValue = (V) values[pos];
      if (objValue == null) {
        break; // no such value
      }

      final K otherKey = getKeyFromValue(objValue);
      if (otherKey.hashCode() == hashCode && otherKey.equals(key)) {
        return objValue; // found a value that matches the given key
      }
    }

    return null;
  }

  protected abstract K getKeyFromValue(V value);

  //
  // Private
  //

  // remove this element and rearrange elements starting from removeIndex+1 to the next value
  private void removeElementAtIndex(int removeIndex) {
    values[removeIndex] = null;
    size -= 1;

    final int readjustCount = getReadjustCount(removeIndex);
    if (readjustCount <= 1) {
      return; // no need to readjust if count of elements that need to be readjusted is zero or one
    }

    // remove elements from these positions and insert them back again to resolve collisions, if any
    final Object[] elements = new Object[readjustCount];
    final int count = values.length;
    for (int i = 0; i < readjustCount; ++i) {
      final int pos = (removeIndex + i + 1) % count;
      elements[i] = values[pos];
      values[pos] = null;
    }

    // insert elements back again
    final int oldSize = size;
    size -= readjustCount;
    for (int i = 0; i < readjustCount; ++i) {
      @SuppressWarnings("unchecked") final V newValue = (V) elements[i];
      add(newValue);
    }
    assert size == oldSize;
  }

  private int getReadjustCount(int removeIndex) {
    int readjustCount = 0;
    final int count = values.length;
    for (int i = removeIndex + 1;; i = (i + 1) % count) {
      if (values[i] == null) {
        break;
      }

      ++readjustCount;
    }

    return readjustCount;
  }

  private void resizeIfNeeded() {
    final int newSize = size + 1;
    if (newSize <= (values.length * loadFactor)) {
      return; // resize is not needed
    }

    final int newCapacity = values.length * 2;
    if (newCapacity < 0 || newCapacity > MAX_CAPACITY) {
      throw new IllegalStateException("Hash table is too big");
    }

    final Object[] newValues = new Object[newCapacity];

    //noinspection ForLoopReplaceableByForEach
    for (int i = 0; i < values.length; ++i) {
      // insert without resolving conflicts
      final Object value = values[i];
      if (value == null) {
        continue;
      }

      @SuppressWarnings("unchecked") final K key = getKeyFromValue((V) value);
      int pos = getPositiveHashCode(key.hashCode(), newCapacity);
      while (newValues[pos] != null) {
        pos = (pos + 1) % newCapacity; // conflict resolution - just move to the next index
      }
      newValues[pos] = value;
    }

    this.values = newValues;
  }

  // returns non-negative value which is strictly less than given maxValue
  private int getPositiveHashCode(int hashCode, int maxValue) {
    final int hash = hashCode % maxValue;
    return hash >= 0 ? hash : -hash;
  }

  // represents K->V map, where key extractor function is represented by the provided function
  private static final class InternalMap<K, V> extends SimpleIntrusiveHashTable<K, V> {
    private final Function<V, K> keyExtractor;

    public InternalMap(int initialCapacity, float loadFactor, Function<V, K> keyExtractor) {
      super(initialCapacity, loadFactor);
      this.keyExtractor = Objects.requireNonNull(keyExtractor, "keyExtractor can't be null");
    }

    @Override
    protected K getKeyFromValue(V value) {
      return keyExtractor.apply(value);
    }
  }

  // represents simple set
  private static final class InternalSet<E> extends SimpleIntrusiveHashTable<E, E> {

    public InternalSet(int initialCapacity, float loadFactor) {
      super(initialCapacity, loadFactor);
    }

    @Override
    protected E getKeyFromValue(E value) {
      return value;
    }
  }

  // iterator
  private static final class Iter<V> implements Iterator<V> {
    private final SimpleIntrusiveHashTable parent;
    private int pos;

    public Iter(SimpleIntrusiveHashTable parent) {
      this.parent = parent;
      setNextPos(0);
    }

    @Override
    public boolean hasNext() {
      return pos < parent.values.length;
    }

    @Override
    public V next() {
      final V value = getElementAtPos();
      setNextPos(pos + 1);
      return value;
    }

    // remove operation breaks the structure and can not be easily implemented without making a lot of
    // copying
//    @Override
//    public void remove() {
//      parent.remove(getElementAtPos()); // potentially breaks the structure
//      setNextPos(pos); // will likely break
//    }

    //
    // Private
    //

    private void setNextPos(int startPos) {
      for (int i = startPos; i < parent.values.length; ++i) {
        if (parent.values[i] != null) {
          pos = i;
          return;
        }
      }

      pos = parent.values.length;
    }

    @SuppressWarnings("unchecked")
    private V getElementAtPos() {
      if (pos < parent.values.length) {
        return (V) parent.values[pos];
      }
      throw new NoSuchElementException();
    }
  }
}
