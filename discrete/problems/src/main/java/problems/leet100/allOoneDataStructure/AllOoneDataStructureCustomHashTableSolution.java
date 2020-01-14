package problems.leet100.allOoneDataStructure;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;

/**
 * 432. All O`one Data Structure
 * https://leetcode.com/problems/all-oone-data-structure/
 *
 * <p>Implement a data structure supporting the following operations:
 *
 * Inc(Key) - Inserts a new key with value 1. Or increments an existing key by 1. Key is guaranteed to be a non-empty string.
 * Dec(Key) - If Key's value is 1, remove it from the data structure. Otherwise decrements an existing key by 1. If the key does not exist, this function does nothing. Key is guaranteed to be a non-empty string.
 * GetMaxKey() - Returns one of the keys with maximal value. If no element exists, return an empty string "".
 * GetMinKey() - Returns one of the keys with minimal value. If no element exists, return an empty string "".
 *
 * Challenge: Perform all these in O(1) time complexity.</p>
 *
 * <p>Runtime: 17 ms, faster than 96.66% of Java online submissions for All O`one Data Structure.
 * Memory Usage: 46.2 MB, less than 14.29% of Java online submissions for All O`one Data Structure.
 * </p>
 */
public class AllOoneDataStructureCustomHashTableSolution {

  public static void main(String[] args) {
    Runnable[] demos = {
        AllOoneDataStructureCustomHashTableSolution::demo0
    };

    if (args.length > 0 && args[0].equals("all")) {
      Arrays.stream(demos).forEach(Runnable::run);
      return;
    }

    int index = args.length > 0 ? Integer.valueOf(args[0]) : 0;
    demos[index].run();
  }

  private static void demo0() {
    AllOne obj = new AllOne();

    String key = "1";
    obj.inc(key);
    checkState("1".equals(obj.getMaxKey()), "min key addition");
    checkState("1".equals(obj.getMinKey()), "max key addition");

    obj.dec(key);
    checkState("".equals(obj.getMaxKey()), "max key after removal");
    checkState("".equals(obj.getMinKey()), "min key after removal");
  }

  /**
   * Standard map + list-based solution.
   * TODO: use skip-list variant, so that each node "knows" where is the next larger / smaller element is,
   *  that'd reduce amortized complexity when multiple nodes are having the same counter value
   */
  @SuppressWarnings("WeakerAccess")
  static final class AllOne {

    static abstract class MaybeNode {
      // position in the linked list that tracks order
      MaybeNode next;
      MaybeNode prev;

      abstract boolean isSentinel();
      abstract String getKey();
    }

    static final class Node extends MaybeNode {
      final String key;
      int value;

      Node(String key) {
        this.key = key;
        this.value = 1;
      }

      @Override
      boolean isSentinel() {
        return false;
      }

      String getKey() {
        return key;
      }

      @Override
      public String toString() {
        return key;
      }
    }

    static final class Sentinel extends MaybeNode {
      final String name;

      Sentinel(String name) {
        this.name = name;
      }

      boolean isSentinel() {
        return true;
      }

      @Override
      String getKey() {
        throw new UnsupportedOperationException("sentinel does not have value");
      }

      @Override
      public String toString() {
        return name;
      }
    }

    private final Map<String, Node> nodes;
    private final Sentinel head = new Sentinel("head");
    private final Sentinel tail = new Sentinel("tail");


    /** Initialize your data structure here. */
    public AllOne() {
      // initialize nodes
      nodes = new HashMap<>(10);

      // initialize sentinels, head points to the highest node, tail - to the lowest
      head.next = head.prev = tail;
      tail.prev = tail.next = head;
    }

    private void insertNewNode(String key) {
      // insert node at a given position into hash table
      final Node newNode = new Node(key);
      final Node existingNode = nodes.put(key, newNode);
      assert existingNode == null;

      // put node into linked list to the very end
      tail.prev.next = newNode;
      newNode.prev = tail.prev;
      tail.prev = newNode;
      newNode.next = tail;
    }

    private void deleteNode(Node node) {
      Node existingNode = nodes.remove(node.key);
      assert existingNode == node;

      // remove node from the linked list
      node.next.prev = node.prev;
      node.prev.next = node.next;
    }

    private void bubbleDownNode(Node node) {
      assert node.value > 0;
      while (!node.next.isSentinel()) {
        final Node next = (Node) node.next;
        if (node.value >= next.value) {
          return;
        }

        // bubble up next node and bubble down current node
        node.prev.next = next;
        next.next.prev = node;

        next.prev = node.prev;
        node.prev = next;
        node.next = next.next;
        next.next = node;
      }
    }

    private void bubbleUpNode(Node node) {
      assert node.value > 0;
      while (!node.prev.isSentinel()) {
        final Node prev = (Node) node.prev;
        if (node.value <= prev.value) {
          return;
        }

        // bubble up next node and bubble down current node
        node.next.prev = prev;
        prev.prev.next = node;

        node.prev = prev.prev;
        prev.prev = node;
        prev.next = node.next;
        node.next = prev;
      }
    }

    private void incOrDec(
        String key,
        boolean isIncrement
    ) {
      Node node = nodes.get(key);

      if (node == null) {
        // node has not been found
        if (isIncrement) {
          insertNewNode(key);
        }
        return;
      }

      // candidate has been found, we now need to execute corresponding action
      if (isIncrement) {
        ++node.value;
        bubbleUpNode(node);
      } else {
        --node.value;
        if (node.value == 0) {
          deleteNode(node);
          return;
        }
        bubbleDownNode(node);
      }
    }

    /** Inserts a new key <Key> with value 1. Or increments an existing key by 1. */
    public void inc(String key) {
      if (key == null || key.isEmpty()) {
        throw new IllegalArgumentException("key");
      }

      incOrDec(key, true);

      checkInvariants();
    }

    /** Decrements an existing key by 1. If Key's value is 1, remove it from the data structure. */
    public void dec(String key) {
      if (key == null || key.isEmpty()) {
        throw new IllegalArgumentException("key");
      }

      incOrDec(key, false);

      checkInvariants();
    }

    /** Returns one of the keys with maximal value. */
    public String getMaxKey() {
      final MaybeNode n = head.next;
      if (n.isSentinel()) {
        return "";
      }
      return ((Node) n).key;
    }

    /** Returns one of the keys with Minimal value. */
    public String getMinKey() {
      final MaybeNode n = tail.prev;
      if (n.isSentinel()) {
        return "";
      }
      return ((Node) n).key;
    }

    private static void checkInvariants() {}

    /*private void checkInvariants() {
      final int size = nodes.size();
      final Set<String> linkedListKeys = new HashSet<>(size * 2);
      int pos = 0;

      final StringBuilder sb = new StringBuilder(100);
      sb.append("head");
      MaybeNode prev = head;
      for (MaybeNode n = head.next; !n.isSentinel(); n = n.next) {
        if (n.prev != prev) {
          throw new IllegalStateException("integrity failure (n.prev != prev); partial state=" + sb.toString());
        }

        linkedListKeys.add(n.getKey());
        ++pos;

        sb.append(", ").append(n.getKey()).append("(c=").append(((Node) n).value).append(")");
        prev = n;
      }
      sb.append(", tail");
      if (tail.prev != prev || tail.prev.next != tail || pos != size) {
        throw new IllegalStateException("integrity failure; partial state=" + sb.toString());
      }

      final Set<String> hashTableKeys = nodes.keySet();

      if (!hashTableKeys.equals(linkedListKeys)) {
        throw new IllegalStateException(String.format("integrity failure; linkedListKeys=%s, hashTableKeys=%s",
            linkedListKeys, hashTableKeys));
      }

      if (!"true".equals(System.getProperty("showIntegrityCheck"))) {
        return;
      }
      System.out.printf("integrity check failure: %s\n", sb.toString());
    }*/
  }

  /**
   * Solution based on custom (intrusive) hash table.
   */
  @SuppressWarnings("WeakerAccess")
  static final class AllOne2 {

    static abstract class MaybeNode {
      // position in the linked list that tracks order
      MaybeNode next;
      MaybeNode prev;

      abstract boolean isSentinel();
      abstract String getKey();
    }

    static final class Node extends MaybeNode {
      final String key;
      int value;
      Node nextConflict;

      Node(String key, Node nextConflict) {
        this.key = key;
        this.value = 1;
        this.nextConflict = nextConflict;
      }

      @Override
      boolean isSentinel() {
        return false;
      }

      String getKey() {
        return key;
      }

      @Override
      public String toString() {
        return key;
      }
    }

    static final class Sentinel extends MaybeNode {
      final String name;

      Sentinel(String name) {
        this.name = name;
      }

      boolean isSentinel() {
        return true;
      }

      @Override
      String getKey() {
        throw new UnsupportedOperationException("sentinel does not have value");
      }

      @Override
      public String toString() {
        return name;
      }
    }

    private static final int INITIAL_CAPACITY = 10;
    private static final float CAPACITY_MULTIPLIER = 2.0f;
    private static final float SIZE_THRESHOLD = 0.625f;

    int size;
    private Node[] nodes;
    private final Sentinel head = new Sentinel("head");
    private final Sentinel tail = new Sentinel("tail");


    /** Initialize your data structure here. */
    public AllOne2() {
      // initialize nodes
      nodes = new Node[INITIAL_CAPACITY];

      // initialize sentinels, head points to the highest node, tail - to the lowest
      head.next = head.prev = tail;
      tail.prev = tail.next = head;
    }

    private void insertNewNode(String key, int pos) {
      // insert node at a given position into hash table
      final Node newNode = new Node(key, nodes[pos]);
      nodes[pos] = newNode;

      // put node into linked list to the very end
      tail.prev.next = newNode;
      newNode.prev = tail.prev;
      tail.prev = newNode;
      newNode.next = tail;

      ++size;
    }

    private void deleteNode(Node node, int pos) {
      // remove node from the linked list
      node.next.prev = node.prev;
      node.prev.next = node.next;

      // remove node from the hash table
      Node startNode = nodes[pos];
      if (startNode == node) {
        startNode = node.nextConflict;
      } else {
        // re-create a list without node above
        for (Node prevNode = startNode;; prevNode = prevNode.nextConflict) {
          if (prevNode.nextConflict == node) {
            prevNode.nextConflict = node.nextConflict;
            break;
          }
        }
      }

      nodes[pos] = startNode;

      // properly reflect the size of a map
      --size;
    }

    private void bubbleDownNode(Node node) {
      assert node.value > 0;
      while (!node.next.isSentinel()) {
        final Node next = (Node) node.next;
        if (node.value >= next.value) {
          return;
        }

        // bubble up next node and bubble down current node
        node.prev.next = next;
        next.next.prev = node;

        next.prev = node.prev;
        node.prev = next;
        node.next = next.next;
        next.next = node;
      }
    }

    private void bubbleUpNode(Node node) {
      assert node.value > 0;
      while (!node.prev.isSentinel()) {
        final Node prev = (Node) node.prev;
        if (node.value <= prev.value) {
          return;
        }

        // bubble up next node and bubble down current node
        node.next.prev = prev;
        prev.prev.next = node;

        node.prev = prev.prev;
        prev.prev = node;
        prev.next = node.next;
        node.next = prev;
      }
    }

    private void incOrDec(
        String key,
        boolean isIncrement
    ) {
      Node node = null;
      final int pos = key.hashCode() % nodes.length;
      for (Node candidate = nodes[pos]; candidate != null; candidate = candidate.nextConflict) {
        if (candidate.getKey().equals(key)) {
          node = candidate;
          break;
        }
      }

      if (node == null) {
        // node has not been found
        if (isIncrement) {
          insertNewNode(key, pos);
        }
        return;
      }

      // candidate has been found, we now need to execute corresponding action
      if (isIncrement) {
        ++node.value;
        bubbleUpNode(node);
      } else {
        --node.value;
        if (node.value == 0) {
          deleteNode(node, pos);
          return;
        }
        bubbleDownNode(node);
      }
    }

    private void maybeGrowHashTable() {
      if (this.size < nodes.length * SIZE_THRESHOLD) {
        return; // table size / capacity ratio still looks reasonable, no resize needed
      }

      final int newCapacity = (int) (nodes.length * CAPACITY_MULTIPLIER);
      assert newCapacity > nodes.length;

      // grow hash table; rehash all the entries
      final Node[] newNodes = new Node[newCapacity];
      for (final Node n : nodes) {
        if (n == null) {
          continue;
        }
        int newPos = n.key.hashCode() % newCapacity;
        while (newNodes[newPos] != null) {
          ++newPos;
        }
        newNodes[newPos] = n;
      }

      this.nodes = newNodes;
    }

    /** Inserts a new key <Key> with value 1. Or increments an existing key by 1. */
    public void inc(String key) {
      if (key == null || key.isEmpty()) {
        throw new IllegalArgumentException("key");
      }

      incOrDec(key, true);
      maybeGrowHashTable();

      integrityCheck("after increment");
    }

    /** Decrements an existing key by 1. If Key's value is 1, remove it from the data structure. */
    public void dec(String key) {
      if (key == null || key.isEmpty()) {
        throw new IllegalArgumentException("key");
      }

      incOrDec(key, false);
      //maybeShrinkHashTable

      integrityCheck("after decrement");
    }

    /** Returns one of the keys with maximal value. */
    public String getMaxKey() {
      final MaybeNode n = head.next;
      if (n.isSentinel()) {
        return "";
      }
      return ((Node) n).key;
    }

    /** Returns one of the keys with Minimal value. */
    public String getMinKey() {
      final MaybeNode n = tail.prev;
      if (n.isSentinel()) {
        return "";
      }
      return ((Node) n).key;
    }

    private static void integrityCheck(String when) {}

//    private void integrityCheck(String when) {
//      final String[] linkedListKeys = new String[size];
//      int pos = 0;
//
//      final StringBuilder sb = new StringBuilder(100);
//      sb.append("head");
//      MaybeNode prev = head;
//      for (MaybeNode n = head.next; !n.isSentinel(); n = n.next) {
//        if (n.prev != prev) {
//          throw new IllegalStateException("integrity failure (n.prev != prev); partial state=" + sb.toString());
//        }
//
//        if (pos >= linkedListKeys.length) {
//          throw new IllegalStateException("integrity failure (pos >= linkedListKeys.length); partial state=" + sb.toString());
//        }
//
//        linkedListKeys[pos] = n.getKey();
//        ++pos;
//
//        sb.append(", ").append(n.getKey()).append("(c=").append(((Node) n).value).append(")");
//        prev = n;
//      }
//      sb.append(", tail");
//      if (tail.prev != prev || tail.prev.next != tail || pos != size) {
//        throw new IllegalStateException("integrity failure; partial state=" + sb.toString());
//      }
//
//      final String[] hashTableKeys = new String[size];
//      pos = 0;
//      for (Node n : nodes) {
//        if (n == null) {
//          continue;
//        }
//
//        for (;;) {
//          if (pos >= hashTableKeys.length) {
//            throw new IllegalStateException("integrity failure (pos >= hashTableKeys.length); partial state=" + sb.toString());
//          }
//
//          hashTableKeys[pos] = n.key;
//          ++pos;
//
//          if (n.nextConflict == null) {
//            break;
//          }
//          n = n.nextConflict;
//        }
//      }
//
//      if (pos != size) {
//        throw new IllegalStateException("integrity failure (incomplete hash table); partial state=" + sb.toString());
//      }
//
//      Arrays.sort(linkedListKeys);
//      Arrays.sort(hashTableKeys);
//
//      if (!Arrays.equals(linkedListKeys, hashTableKeys)) {
//        throw new IllegalStateException(String.format("integrity failure; linkedListKeys=%s, hashTableKeys=%s",
//            Arrays.toString(linkedListKeys), Arrays.toString(hashTableKeys)));
//      }
//
//      if (!"true".equals(System.getProperty("showIntegrityCheck"))) {
//        return;
//      }
//      System.out.printf("integrity check %s: %s\n", when, sb.toString());
//    }
  }
}
