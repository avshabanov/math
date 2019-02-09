package problems.datastructures.lfu;

import java.util.Arrays;
import java.util.Comparator;

/**
 * Solution for LFU (Least Frequently Used) Cache problem - https://leetcode.com/problems/lfu-cache/
 */
public final class LFUCacheStructure {

  static final class LFUCache {
    static final int NOT_FOUND_VALUE_MARKER = -1;

    static final long ACCESS_STEP = 4_000_000_000L;

    static final class Entry {
      long usageCount = 0;
      final int key;
      final int value;

      public Entry(final int key, int value) {
        this.key = key;
        this.value = value;
      }
    }

    static final Comparator<Entry> ENTRY_COMPARATOR = Comparator.comparingLong(e -> e.usageCount);

    final Entry[] entries;
    int size = 0;
    long accessCount = 0;

    public LFUCache(int capacity) {
      this.entries = new Entry[capacity];
    }

    public int get(int key) {
      ++accessCount;
      for (final Entry e : entries) {
        if (e != null && e.key == key) {
          e.usageCount = e.usageCount + ACCESS_STEP;

          // sort to account entries order
          Arrays.sort(entries, ENTRY_COMPARATOR);

          return e.value;
        }
      }

      return NOT_FOUND_VALUE_MARKER;
    }

    public void put(int key, int value) {

    }
  }

  //
  // Demo
  //

  public static final class Demo1 {
    public static void main(String[] args) {

    }
  }
}
