
import util.LockFreeQueueVerifier;

import java.util.AbstractQueue;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.atomic.AtomicReference;

/**
 * TODO: insertion test
 *
 * @author Alexander Shabanov
 */
public final class SimpleLockFreeQueueExample {
  public static void main(String[] args) {
    final LockFreeQueueVerifier verifier = new LockFreeQueueVerifier(1000, new SimpleLockFreeQueue<>());
    verifier.start();
  }

  //
  // Private
  //

  private static final class SimpleLockFreeQueue<E> extends AbstractQueue<E> {

    private static final class Node <E> {
      private final E item;
      private final AtomicReference<Node<E>> next;

      Node(E item, Node<E> next) {
        this.item = item;
        this.next = new AtomicReference<>(next);
      }
    }

    private AtomicReference<Node<E>> head
        = new AtomicReference<>(new Node<>(null, null));
    private AtomicReference<Node<E>> tail = head;

    @Override
    public Iterator<E> iterator() {
      // TODO: reusable
      Node<E> h;
      Node<E> t;
      while (true) {
        h = head.get();
        t = tail.get();
        if (h == head.get() && t == tail.get()) {
          break;
        }
      }

      return new SimpleQueueIterator<>(h, t);
    }

    @Override
    public int size() {
      // TODO: reusable
      Node<E> h;
      Node<E> t;
      while (true) {
        h = head.get();
        t = tail.get();
        if (h == head.get() && t == tail.get()) {
          break;
        }
      }

      int s = 0;
      while (h != t) {
        ++s;
        h = h.next.get();
      }
      return s;
    }

    @Override
    public boolean offer(E e) {
      Node<E> newNode = new Node<E>(e, null);
      while (true) {
        Node<E> curTail = tail.get();
        Node<E> residue = curTail.next.get();
        if (curTail == tail.get()) {
          if (residue == null) /* A */ {
            if (curTail.next.compareAndSet(null, newNode)) /* C */ {
              tail.compareAndSet(curTail, newNode) /* D */ ;
              return true;
            }
          } else {
            tail.compareAndSet(curTail, residue) /* B */;
          }
        }
      }
    }

    @Override
    public E poll() {
      while (true) {
        // TODO: reusable
        Node<E> h;
        Node<E> t;
        while (true) {
          h = head.get();
          t = tail.get();
          if (h == head.get() && t == tail.get()) {
            break;
          }
        }

        if (h != t) {
          if (!head.compareAndSet(h, h.next.get())) {
            continue;
          }

          return h.item;
        }

        throw new NoSuchElementException();
      }
    }

    @Override
    public E peek() {
      // TODO: reusable
      Node<E> h;
      Node<E> t;
      while (true) {
        h = head.get();
        t = tail.get();
        if (h == head.get() && t == tail.get()) {
          break;
        }
      }

      if (h != t) {
        return h.item;
      }

      return null;
    }

    //
    // Private
    //

    private static final class SimpleQueueIterator<E> implements Iterator<E> {
      Node<E> h;
      final Node<E> t;

      public SimpleQueueIterator(Node<E> h, Node<E> t) {
        this.h = h;
        this.t = t;
      }

      @Override
      public boolean hasNext() {
        return h != t;
      }

      @Override
      public E next() {
        if (h == t) {
          throw new NoSuchElementException();
        }
        final E e = h.item;
        h = h.next.get();
        return e;
      }
    }
  }
}
