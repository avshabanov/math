package problems.leet100.challenges.c2020_04.w4;

import java.util.HashMap;
import java.util.Map;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/531/week-4/3309/
 * <p>Design and implement a data structure for Least Recently Used (LRU) cache.
 * It should support the following operations: get and put.
 *
 * get(key) - Get the value (will always be positive) of the key if the key exists in the cache, otherwise return -1.
 * put(key, value) - Set or insert the value if the key is not already present. When the cache reached its capacity,
 * it should invalidate the least recently used item before inserting a new item.
 *
 * The cache is initialized with a positive capacity.
 *
 * Follow up:
 * Could you do both operations in O(1) time complexity?</p>
 */
public class LRUCacheSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      final LRUCache cache = new LRUCache(2);
      cache.put(1, 1);
      cache.put(2, 2);
      System.out.printf("cache.get(1) = %d\n", cache.get(1));         // returns 1
      cache.put(3, 3);    // evicts key 2
      System.out.printf("cache.get(2) = %d\n", cache.get(2));         // returns -1 (not found)
      cache.put(4, 4);    // evicts key 1
      System.out.printf("cache.get(1) = %d\n", cache.get(1));         // returns -1 (not found)
      System.out.printf("cache.get(3) = %d\n", cache.get(3));         // returns 3
      System.out.printf("cache.get(4) = %d\n", cache.get(4));         // returns 4
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      final LRUCache cache = new LRUCache(2);
      cache.get(2);
      cache.put(2, 6);
      cache.get(1);
      cache.put(1, 5);
      cache.put(1, 2);
      cache.get(1);
      cache.get(2);
    }
  }

  private static final class LRUCache {

    private static final class Node {
      private Node prev;
      private Node next;
      private int key;
      private int value;
    }

    private Node sentinel;
    private int size;
    private final int capacity;
    private final Map<Integer, Node> map = new HashMap<>();

    public LRUCache(int capacity) {
      if (capacity <= 0) {
        throw new IllegalArgumentException("illegal capacity");
      }
      this.capacity = capacity;
      this.sentinel = new Node();
      this.sentinel.prev = this.sentinel.next = this.sentinel;
    }

    public int get(int key) {
      final Node node = this.map.get(key);
      if (node == null) {
        return -1;
      }

      refreshNode(node);

      return node.value;
    }

    public void put(int key, int value) {
      Node node = map.get(key);
      if (node != null) {
        // existing element: refresh
        node.value = value;
        refreshNode(node);
      } else if (this.size == this.capacity) {
        // exclude last element
        node = sentinel.prev;
        map.remove(node.key);
        node.key = key;
        node.value = value;
        refreshNode(node);
      } else {
        // insert new element
        ++this.size;
        node = new Node();
        node.key = key;
        node.value = value;
        appendToHead(node);
      }

      this.map.put(key, node);
    }

    private void refreshNode(Node node) {
      // remove node from its current position
      node.prev.next = node.next;
      node.next.prev = node.prev;

      appendToHead(node);
    }

    private void appendToHead(Node node) {
      // put node to the head of the list
      node.next = sentinel.next;
      node.prev = sentinel;
      node.next.prev = node;
      sentinel.next = node;
    }
  }
}
