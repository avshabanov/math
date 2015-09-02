import util.LockFreeStack;
import util.LockFreeStackVerifier;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Simplest implementation of lock free stack.
 *
 * Sample output:
 *
 * <code>
 *   [PASSED] Stack contains the same amount of elements that have been passed
 *   [PASSED] Stack is now empty
 * </code>
 */
public final class SimpleLockFreeStackExample {

  public static void main(String[] args) {
    final LockFreeStackVerifier verifier = new LockFreeStackVerifier(1000, new SimpleLockFreeStack<>());
    verifier.start();
  }

  //
  // Private
  //

  private static final class SimpleLockFreeStack<T> implements LockFreeStack<T> {
    private volatile AtomicReference<Node<T>> head = new AtomicReference<>();

    @Override
    public void push(T element) {
      final Node<T> candidate = new Node<>(element, null);

      while (true) {
        final Node<T> headSnapshot = head.get();
        candidate.next = headSnapshot; // update candidate's next snapshot
        if (head.compareAndSet(headSnapshot, candidate)) {
          break;
        }
      }
    }

    @Override
    public T pop(T defaultElement) {
      T value = defaultElement;

      while (true) {
        Node<T> candidate = head.get();
        if (candidate == null) {
          break;
        }

        value = candidate.value;
        if (head.compareAndSet(candidate, candidate.next)) {
          break;
        }
      }

      return value;
    }

    @Override
    public int size() {
      int result = 0;
      for (Node<T> it = head.get(); it != null; it = it.next) {
        ++result;
      }
      return result;
    }

    @Override
    public List<T> toList() {
      final List<T> result = new ArrayList<>(size());
      for (Node<T> it = head.get(); it != null; it = it.next) {
        result.add(it.value);
      }

      return result;
    }

    //
    // Private
    //

    private static final class Node<T> {
      final T value;
      volatile Node<T> next; // effectively immutable once node is inserted

      public Node(T value, Node<T> next) {
        this.value = value;
        this.next = next;
      }
    }
  }
}
