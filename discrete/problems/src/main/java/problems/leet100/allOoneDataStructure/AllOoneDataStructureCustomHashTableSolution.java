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
   */
  @SuppressWarnings("WeakerAccess")
  static final class AllOne {

    private final Map<String, MinMaxTrackingList.Element<String>> nodes;
    private final MinMaxTrackingList<String> minMaxTrackingList;


    /** Initialize your data structure here. */
    public AllOne() {
      // initialize nodes
      nodes = new HashMap<>(10);
      //minMaxTrackingList = new SimpleMinMaxTrackingList<>(); simpler solution with O(n) complexity for inc and dec
      // when multiple elements get inserted

      // skip list gives truly O(1) solution
      minMaxTrackingList = new SkipMinMaxList<>();
    }

    /** Inserts a new key <Key> with value 1. Or increments an existing key by 1. */
    public void inc(String key) {
      if (key == null || key.isEmpty()) {
        throw new IllegalArgumentException("key");
      }

      final MinMaxTrackingList.Element<String> node = nodes.get(key);
      if (node == null) {
        final MinMaxTrackingList.Element<String> newNode = minMaxTrackingList.add(key);
        final MinMaxTrackingList.Element<String> existingNode = nodes.put(key, newNode);
        assert existingNode == null;
        return;
      }

      minMaxTrackingList.inc(node);
    }

    /** Decrements an existing key by 1. If Key's value is 1, remove it from the data structure. */
    public void dec(String key) {
      if (key == null || key.isEmpty()) {
        throw new IllegalArgumentException("key");
      }

      final MinMaxTrackingList.Element<String> node = nodes.get(key);
      if (node == null) {
        return;
      }

      if (node.getValue() == 1) {
        // node needs to be removed
        minMaxTrackingList.remove(node);
        nodes.remove(key);
        return;
      }

      minMaxTrackingList.dec(node);
    }

    /** Returns one of the keys with maximal value. */
    public String getMaxKey() {
      return minMaxTrackingList.getMaxKey("");
    }

    /** Returns one of the keys with Minimal value. */
    public String getMinKey() {
      return minMaxTrackingList.getMinKey("");
    }
  }

  interface MinMaxTrackingList<T> {
    interface Element<T> {
      T getKey();
      int getValue();
    }

    Element<T> add(T key);
    void remove(Element<T> element);
    void inc(Element<T> element);
    void dec(Element<T> element);
    T getMinKey(T defaultKey);
    T getMaxKey(T defaultKey);
  }

  static final class SimpleMinMaxTrackingList<T> implements MinMaxTrackingList<T> {
    private static abstract class MaybeElement<T> implements Element<T> {
      MaybeElement<T> prev;
      MaybeElement<T> next;

      abstract boolean isElement();

      @Override
      public T getKey() {
        throw new UnsupportedOperationException();
      }

      @Override
      public int getValue() {
        throw new UnsupportedOperationException();
      }
    }

    private static final class Sentinel<T> extends MaybeElement<T> {
      boolean isElement() {
        return false;
      }

      @Override
      public String toString() {
        return "sentinel#" + System.identityHashCode(this);
      }
    }

    private static final class ElementImpl<T> extends MaybeElement<T> {
      private final T key;
      private int value;

      ElementImpl(T key) {
        this.key = key;
        this.value = 1;
      }

      @Override
      public T getKey() {
        return key;
      }

      @Override
      public int getValue() {
        return value;
      }

      @Override
      boolean isElement() {
        return true;
      }

      @Override
      public String toString() {
        return String.valueOf(key);
      }
    }

    private final Sentinel<T> head = new Sentinel<>();
    private final Sentinel<T> tail = new Sentinel<>();

    @SuppressWarnings("WeakerAccess")
    public SimpleMinMaxTrackingList() {
      head.next = head.prev = tail;
      tail.prev = tail.next = head;
    }

    @Override
    public Element<T> add(T key) {
      final ElementImpl<T> element = new ElementImpl<>(key);

      element.prev = tail.prev;
      element.next = tail;

      tail.prev.next = element;
      tail.prev = element;

      return element;
    }

    @Override
    public void remove(Element<T> element) {
      final ElementImpl<T> e = (ElementImpl<T>) element;
      e.prev.next = e.next;
      e.next.prev = e.prev;
    }

    @Override
    public void inc(Element<T> element) {
      final ElementImpl<T> node = (ElementImpl<T>) element;

      ++node.value;
      assert node.value > 0;

      while (node.prev.isElement()) {
        final MaybeElement<T> prev = node.prev;
        if (node.value <= prev.getValue()) {
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

    @Override
    public void dec(Element<T> element) {
      final ElementImpl<T> node = (ElementImpl<T>) element;

      --node.value;
      assert node.value > 0;

      while (node.next.isElement()) {
        final MaybeElement<T> next = node.next;
        if (node.value >= next.getValue()) {
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

    @Override
    public T getMinKey(T defaultKey) {
      final MaybeElement<T> e = this.tail.prev;
      return e.isElement() ? e.getKey() : defaultKey;
    }

    @Override
    public T getMaxKey(T defaultKey) {
      final MaybeElement<T> e = this.head.next;
      return e.isElement() ? e.getKey() : defaultKey;
    }
  }

  static final class SkipMinMaxList<T> implements MinMaxTrackingList<T> {

    private final Compartment<T> head = new Compartment<>(0);
    private final Compartment<T> tail = new Compartment<>(-1);

    public SkipMinMaxList() {
      this.head.next = this.head.prev = this.tail;
      this.tail.next = this.tail.prev = this.head;
    }

    @Override
    public Element<T> add(T key) {
      final Compartment<T> compartment;
      if (this.tail.prev.isSentinel() || this.tail.prev.value != 1) {
        assert this.tail.prev.isSentinel() || this.tail.prev.value > 1;
        compartment = new Compartment<>(1);

        tail.prev.next = compartment;
        compartment.next = tail;
        compartment.prev = tail.prev;
        tail.prev = compartment;
      } else {
        compartment = this.tail.prev;
      }

      final Compartment.Node<T> node = new Compartment.Node<>(key);
      prependNode(compartment, node);
      return node;
    }

    @Override
    public void remove(Element<T> element) {
      final Compartment.Node<T> node = (Compartment.Node<T>) element;
      removeNode(node);
    }

    // truly O(1) inc
    @Override
    public void inc(Element<T> element) {
      final Compartment.Node<T> node = (Compartment.Node<T>) element;
      final int nextValue = node.owner.value + 1;

      final Compartment<T> prevOwner = node.owner.prev;
      removeNode(node);

      // either move node to the next compartment or create a new one
      final Compartment<T> newOwner;
      if (prevOwner.isSentinel() || prevOwner.value != nextValue) {
        // there is no compartment that can host this node, create a new one
        assert prevOwner == head || prevOwner.value > nextValue;
        newOwner = new Compartment<>(nextValue);
        newOwner.prev = prevOwner;
        newOwner.next = prevOwner.next;

        prevOwner.next.prev = newOwner;
        prevOwner.next = newOwner;
      } else {
        newOwner = prevOwner;
      }

      prependNode(newOwner, node);
    }

    // truly O(1) dec
    @Override
    public void dec(Element<T> element) {
      final Compartment.Node<T> node = (Compartment.Node<T>) element;
      final int nextValue = node.owner.value - 1;

      final Compartment<T> nextOwner = node.owner.next;
      removeNode(node);

      // either move node to the next compartment or create a new one
      final Compartment<T> newOwner;
      if (nextOwner.isSentinel() || nextOwner.value != nextValue) {
        // there is no compartment that can host this node, create a new one
        assert nextOwner == tail || nextOwner.value < nextValue;
        newOwner = new Compartment<>(nextValue);
        newOwner.next = nextOwner;
        newOwner.prev = nextOwner.prev;

        nextOwner.prev.next = newOwner;
        nextOwner.prev = newOwner;
      } else {
        newOwner = nextOwner;
      }

      prependNode(newOwner, node);
    }

    @Override
    public T getMinKey(T defaultKey) {
      return this.tail.prev.isSentinel() ? defaultKey : this.tail.prev.head.next.key;
    }

    @Override
    public T getMaxKey(T defaultKey) {
      return this.head.next.isSentinel() ? defaultKey : this.head.next.head.next.key;
    }

    //
    // Private
    //

    private static <T> void prependNode(Compartment<T> owner, Compartment.Node<T> node) {
      node.owner = owner;

      node.prev = owner.head;
      node.next = owner.head.next;

      owner.head.next.prev = node;
      owner.head.next = node;
    }

    private static <T> void removeNode(Compartment.Node<T> node) {
      node.prev.next = node.next;
      node.next.prev = node.prev;
      if (node.owner.head.next == node.owner.tail) {
        // no more nodes in this compartment, exclude it from the list
        node.owner.prev.next = node.owner.next;
        node.owner.next.prev = node.owner.prev;
      }
      node.owner = null;
    }

    private static final class Compartment<T> {
      final int value;
      final Node<T> head = new Node<>(null);
      final Node<T> tail = new Node<>(null);

      private Compartment<T> next;
      private Compartment<T> prev;

      boolean isSentinel() {
        return head.next == tail;
      }

      Compartment(int value) {
        this.value = value;
        this.head.next = this.head.prev = this.tail;
        this.tail.next = this.tail.prev = this.head;
      }

      @Override
      public String toString() {
        return "#" + value;
      }

      private static final class Node<T> implements Element<T> {
        private Node<T> prev;
        private Node<T> next;
        private final T key;
        private Compartment<T> owner;

        Node(T key) {
          this.key = key;
        }

        @Override
        public T getKey() {
          return key;
        }

        @Override
        public int getValue() {
          return owner.value;
        }
      }
    }
  }
}
