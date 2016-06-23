import java.util.*;

/**
 * Simple queue collection demo based on singly linked list.
 * <p>Sample run:</p>
 * <pre>
 * [1] q=[1, 2, 3, 4], dequeue=0
 * [2] q=[]
 * [3] q=[5, 6, 7, 8]
 * [4] q=[5, 6, 7, 9]
 * [5] q=[9]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class QueueExample {

  public static void main(String[] args) {
    demo1();
  }

  public static void demo1() {
    final SimpleQueue<String> q = new SimpleQueueImpl<>();
    q.addAll(Arrays.asList("0", "1", "2", "3"));

    q.enqueue("4");
    final String first = q.dequeue();

    assert Arrays.equals(new String[] {"1", "2", "3", "4"},
        q.toArray(new String[q.size()]));

    System.out.println("[1] q=" + q + ", dequeue=" + first);

    q.removeAll(Arrays.asList("1", "2", "3", "4"));

    assert q.isEmpty();
    System.out.println("[2] q=" + q);

    q.enqueue("5");
    q.enqueue("6");
    q.enqueue("7");
    q.enqueue("8");
    System.out.println("[3] q=" + q);

    q.remove("8");
    q.add("9");
    System.out.println("[4] q=" + q);

    q.removeAll(Arrays.asList("6", "7", "5"));
    System.out.println("[5] q=" + q);
  }

  //
  // Interface and implementation
  //

  /** Interface. */
  private interface SimpleQueue<T> extends Collection<T> {

    T dequeue();

    void enqueue(T value);
  }

  /** Implementation. */
  private static final class SimpleQueueImpl<T> extends AbstractCollection<T> implements SimpleQueue<T> {
    Node<T> head; // for dequeue operation
    Node<T> tail; // for enqueue operation

    @Override
    public void enqueue(T value) {
      final Node<T> node = new Node<>();
      node.value = value;

      if (tail != null) {
        tail.next = node;
      } else {
        head = node;
      }
      tail = node;
    }

    @Override
    public T dequeue() {
      if (head == null) {
        throw new IllegalStateException("Queue is empty");
      }

      final T value = head.value;
      head = head.next;
      if (head == null) {
        tail = null;
      }
      return value;
    }

    @Override
    public boolean add(T value) {
      enqueue(value);
      return true;
    }

    @SuppressWarnings("NullableProblems")
    @Override
    public Iterator<T> iterator() {
      //noinspection unchecked
      return new SimpleQueueIteratorImpl();
    }

    @Override
    public int size() {
      int size = 0;
      for (Node<T> n = head; n != null; n = n.next) {
        ++size;
      }
      return size;
    }

    private static final class Node<T> {
      T value;
      Node<T> next;
    }

    private final class SimpleQueueIteratorImpl implements Iterator<T> {
      private Node<T> cursor;

      public SimpleQueueIteratorImpl() {
        this.cursor = head;
      }

      @Override
      public boolean hasNext() {
        return cursor != null;
      }

      @Override
      public T next() {
        if (cursor != null) {
          final T value = cursor.value;
          cursor = cursor.next;
          return value;
        }

        throw new NoSuchElementException();
      }

      // TODO: implement O(1) solution at the expense of adding extra field to this iterator
      @Override
      public void remove() {
        if (cursor == head) {
          throw new NoSuchElementException(); // very beginning
        }

        if (dropMe(head)) { // recursively drop element
          dequeue();
        }
      }

      // TODO: simplify with non-recursive O(1) algorithm (see above)
      private boolean dropMe(Node<T> current) {
        if (current == null) {
          return false;
        }

        if (current.next == cursor) {
          return true;
        }

        if (dropMe(current.next)) {
          if (current.next == tail) {
            tail = current;
          }
          current.next = current.next.next;
        }

        return false;
      }
    }
  }
}
