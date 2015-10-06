import util.LockFreeQueueVerifier;

import java.util.AbstractQueue;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Queue;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Tests naïve implementation of lock-free queue.
 *
 * Sample output:
 *
 * <code>
 * dTime: 1638862973ns [PASSED] Queue is empty after simultaneous add-remove
 * dTime: 82798181ns [PASSED] Queue contains the same amount of elements that have been passed
 * dTime: 66725079ns [PASSED] Queue is now empty
 * [STATS] Lists dropped=3504, wasted=1504
 * dTime: 107463335ns [PASSED] Queue is empty after simultaneous add-remove
 * dTime: 98542445ns [PASSED] Queue contains the same amount of elements that have been passed
 * dTime: 66857827ns [PASSED] Queue is now empty
 * [STATS] Lists dropped=6827, wasted=2827
 * </code>
 *
 * @author Alexander Shabanov
 */
public final class SimpleLockFreeQueueExample {
  public static void main(String[] args) {
    final Queue<Integer> q = new SimpleLockFreeQueue<>();
    if ((args.length > 1 && "queueTest".equals(args[0])) || System.getProperty("test.queue") != null) {
      q.add(1);
      q.add(2);
      q.add(3);
      System.out.println("[1] q=" + q);

      q.remove();
      System.out.println("[2] q=" + q);
      q.remove();
      System.out.println("[3] q=" + q);
      q.remove();
      System.out.println("[4] q=" + q);

      q.add(4);
      System.out.println("[5] q=" + q);

      return;
    }

    new LockFreeQueueVerifier(1000, q).start();
    printStats(q);
    new LockFreeQueueVerifier(1000, q).start();
    printStats(q);
  }

  //
  // Private
  //

  private static void printStats(Queue<?> queue) {
    if (queue instanceof SimpleLockFreeQueue) {
      final SimpleLockFreeQueue<?> q = (SimpleLockFreeQueue) queue;
      System.out.println("[STATS] Lists dropped=" + q.getDroppedListCount() + ", wasted=" + q.getWastedListCount());
    }
  }
}

/**
 * Memory unfriendly queue, best suited for relatively small queues with frequent removals.
 *
 * This implementation is extremely ineffective when a lot of parallel threads try to add elements simultaneously - see
 * also wasted lists count returned by {@link #getWastedListCount()} - this number gives an idea how many lists
 * constructed internally were discarded. In single thread-execution scenario this number will be zero, however this
 * number will grow linearly depending on how many threads are modifying collection simultaneously.
 *
 * Also this data structure has O(n) time complexity for insertion and O(n*k) memory consumption where k is number of
 * threads simultaneously modifying the queue and n - number of elements in a queue.
 *
 * Timing comparison against the standard JDK's {@link java.util.concurrent.ConcurrentLinkedQueue} implementation is
 * given in README.md
 *
 * However it removal operation is just O(1) for both memory consumption and time complexity.
 *
 * @param <E> Type of element
 */
final class SimpleLockFreeQueue<E> extends AbstractQueue<E> {

  private static final class Node<E> {
    private final E item;
    private final Node<E> next;

    Node(E item, Node<E> next) {
      this.item = item;
      this.next = next;
    }
  }

  private final AtomicReference<Node<E>> head = new AtomicReference<>(null);

  // for statistics only (how many lists were dropped/completely wasted during execution)
  private final AtomicInteger droppedLists = new AtomicInteger();
  private final AtomicInteger wastedLists = new AtomicInteger();

  public int getDroppedListCount() {
    return droppedLists.get();
  }

  public int getWastedListCount() {
    return wastedLists.get();
  }

  @SuppressWarnings("NullableProblems")
  @Override
  public Iterator<E> iterator() {
    return new SimpleQueueIterator<>(head.get());
  }

  @Override
  public int size() {
    int result = 0;
    for (Node<E> i = head.get(); i != null; i = i.next) {
      ++result;
    }
    return result;
  }

  @Override
  public boolean offer(E e) {
    Node<E> newNode = new Node<>(e, null);
    int listsDropped = 1;
    for (;;) {
      final Node<E> h = head.get();
      final Node<E> newHead = appendNode(h, newNode);
      if (head.compareAndSet(h, newHead)) {
        break;
      }

      ++listsDropped;
    }

    droppedLists.addAndGet(listsDropped);
    wastedLists.addAndGet(listsDropped - 1);

    return true;
  }

  private static <E> Node<E> appendNode(Node<E> head, Node<E> newTail) {
    return head != null ? new Node<>(head.item, appendNode(head.next, newTail)) : newTail;
  }

  @Override
  public E poll() {
    while (true) {
      Node<E> h = head.get();
      if (h == null) {
        throw new NoSuchElementException();
      } else if (head.compareAndSet(h, h.next)) {
        return h.item;
      }
    }
  }

  @Override
  public E peek() {
    Node<E> h = head.get();
    return h != null ? h.item : null;
  }

  //
  // Private
  //

  private static final class SimpleQueueIterator<E> implements Iterator<E> {
    Node<E> iter;

    public SimpleQueueIterator(Node<E> iter) {
      this.iter = iter;
    }

    @Override
    public boolean hasNext() {
      return iter != null;
    }

    @Override
    public E next() {
      if (iter == null) {
        throw new NoSuchElementException();
      }
      final E e = iter.item;
      iter = iter.next;
      return e;
    }
  }
}
