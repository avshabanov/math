import util.LockFreeStack;
import util.LockFreeStackVerifier;

import java.util.ArrayList;
import java.util.List;

/**
 * This is KNOWN AS BEING BROKEN.
 * It is here for illustrative purposes only.
 *
 * The test output looks as follows (on 2014 Mac Book Pro) -
 * <code>
 *   [FAILED] Stack contains different amount of elements that have been passed, actual=318, expected=1000
 *   [FAILED] Stack is not empty, size=23, countOfPopFailures=0
 * </code>
 */
public final class NaiveAndBrokenLockFreeStackExample {

  public static void main(String[] args) {
    final LockFreeStackVerifier verifier = new LockFreeStackVerifier(1000, new NaiveLockFreeStack<>());
    verifier.start();
  }

  //
  // Private
  //

  private static final class NaiveLockFreeStack<T> implements LockFreeStack<T> {
    private volatile Node<T> head = null;

    @Override
    public void push(T element) {
      final Node<T> prevHead = head;
      head = new Node<>(element, prevHead);
    }

    @Override
    public T pop(T defaultElement) {
      final Node<T> prevHead = head;
      if (prevHead == null) {
        return defaultElement;
      }

      this.head = prevHead.next;
      return prevHead.value;
    }

    @Override
    public int size() {
      int result = 0;
      for (Node<T> it = head; it != null; it = it.next) {
        ++result;
      }
      return result;
    }

    @Override
    public List<T> toList() {
      final List<T> result = new ArrayList<>(size());
      for (Node<T> it = head; it != null; it = it.next) {
        result.add(it.value);
      }

      return result;
    }

    //
    // Private
    //

    private static final class Node<T> {
      final T value;
      final Node<T> next;

      public Node(T value, Node<T> next) {
        this.value = value;
        this.next = next;
      }
    }
  }
}
