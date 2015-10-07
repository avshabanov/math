import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

/**
 * Simple heap data structure built on top of fixed-size array.
 * See also https://en.wikipedia.org/wiki/Heap_(data_structure)
 */
public class ArrayBasedHeapExample {
  public static void main(String[] args) {
    testIncreasing();
    testDecreasing();
    testShuffled();
  }

  //
  // Private
  //

  private static void testIncreasing() {
    final Heap<Character> heap = new FixedArrayBasedHeap<>(10);
    heap.addAll(Arrays.asList('a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'));
    System.out.println("Peek=" + heap.peek() + ", Removed=" + heap.removeAll());
  }

  private static void testDecreasing() {
    final Heap<Character> heap = new FixedArrayBasedHeap<>(10);
    heap.addAll(Arrays.asList('h', 'g', 'f', 'e', 'd', 'c', 'b', 'a'));
    System.out.println("Peek=" + heap.peek() + ", Removed=" + heap.removeAll());
  }

  private static void testShuffled() {
    final Heap<Character> heap = new FixedArrayBasedHeap<>(10);
    heap.addAll(Arrays.asList('h', 'b', 'f', 'd', 'e', 'c', 'g', 'a'));
    System.out.println("Peek=" + heap.peek() + ", Removed=" + heap.removeAll());
  }

  /**
   * Simple equivalent of the JDK's {@link java.util.PriorityQueue}.
   *
   * @param <E> Type of elements in the heap
   */
  private interface Heap<E extends Comparable<E>> {
    /** Adds a new element to the heap */
    void add(E element);

    default void addAll(Collection<? extends E> elements) {
      elements.forEach(this::add);
    }

    /**
     * Removes top element from this heap
     *
     * @return Element on top of the heap
     */
    E remove();

    default List<E> removeAll() {
      final List<E> result = new ArrayList<>();
      while (!isEmpty()) {
        result.add(remove());
      }
      return result;
    }

    /**
     * @return Element on top of the heap
     */
    E peek();

    int size();

    default boolean isEmpty() {
      return size() == 0;
    }
  }

  /**
   * An implementation of the heap, based on fixed-size array.
   *
   * @param <E> Type of elements in this heap
   */
  private static final class FixedArrayBasedHeap<E extends Comparable<E>> implements Heap<E> {
    private final Comparable[] buffer;
    private int size;

    public FixedArrayBasedHeap(final int capacity) {
      this.buffer = new Comparable[capacity];
    }

    @Override
    public void add(E element) {
      if (element == null) {
        throw new NullPointerException("element is null");
      }

      final int prevSize = size;
      final int newSize = size + 1;

      if (newSize >= (buffer.length - 1)) {
        throw new IllegalStateException("Heap full");
      }

      this.buffer[prevSize] = element;
      this.size = newSize;

      bubbleUp(prevSize);
    }

    @Override
    public int size() {
      return size;
    }

    @Override
    public E remove() {
      // what do want return?
      final E result = peek();

      // get rid of the last leaf/decrement
      final int newSize = size - 1;
      buffer[0] = buffer[newSize];
      buffer[newSize] = null;
      size = newSize;

      bubbleDown(0);

      return result;
    }

    @Override
    public E peek() {
      if (isEmpty()) {
        throw new IllegalStateException("Heap empty");
      }
      return at(0);
    }

    //
    // Private
    //

    @SuppressWarnings("unchecked")
    private E at(int index) {
      return (E) buffer[index];
    }

    private void bubbleUp(int index) {
      for (;;) {
        if (!hasParent(index)) {
          break;
        }

        final E child = at(index);
        final int parentIndex = getParentIndex(index);
        final E parent = at(parentIndex);
        if (parent.compareTo(child) > 0) {
          break;
        }

        buffer[parentIndex] = child;
        buffer[index] = parent;

        index = parentIndex;
      }
    }

    private void bubbleDown(int index) {
      // bubble down
      while (hasLeftChild(index)) {
        // which of my children is smaller?
        int greaterChildIndex = getLeftIndex(index);

        // bubble with the greater child, if possible
        if (hasRightChild(index)) {
          final int rightChildIndex = getRightIndex(index);
          if (at(greaterChildIndex).compareTo(at(rightChildIndex)) < 0) {
            greaterChildIndex = rightChildIndex;
          }
        }

        final E element = at(index);
        final E smallerChildElement = at(greaterChildIndex);
        if (element.compareTo(smallerChildElement) >= 0) {
          break; // no swap needs to be made
        }

        buffer[greaterChildIndex] = element;
        buffer[index] = smallerChildElement;
        index = greaterChildIndex;
      }
    }

    private static boolean hasParent(int index) {
      return index > 0;
    }


    private static int getLeftIndex(int index) {
      return index * 2 + 1;
    }


    private static int getRightIndex(int index) {
      return index * 2 + 2;
    }


    private boolean hasLeftChild(int index) {
      return getLeftIndex(index) < size;
    }


    private boolean hasRightChild(int index) {
      return getRightIndex(index) < size;
    }

    private int getParentIndex(int index) {
      return index / 2;
    }

//    private void printTree(int index, int indent) {
//      if (index >= size) {
//        return;
//      }
//
//      printTree(getLeftIndex(index), indent + 1);
//      for (int i = 0; i < indent; ++i) {
//        System.out.print(' ');
//      }
//      System.out.println(at(index));
//      printTree(getRightIndex(index), indent + 1);
//    }
  }
}
