import java.util.Arrays;
import java.util.NoSuchElementException;

/**
 * The problem: implement deque on top of the array.
 *
 * Sample run:
 * <pre>
 * last element in deque=4
 * deque content=[0, 1, 2, 3]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class ArrayDequeExample {

  public static void main(String[] args) {
    demo();
  }

  public static void demo() {
    final SimpleDeque<String> d = new SimpleArrayDeque<>();
    d.addFirst("2");
    d.addFirst("1");
    d.addLast("3");
    d.addFirst("0");
    d.addLast("4");

    final String e = d.popLast();
    System.out.println("last element in deque=" + e);

    final String[] arr = popToArray(d);
    System.out.println("deque content=" + Arrays.toString(arr));
  }

  public static String[] popToArray(SimpleDeque<String> d) {
    final String[] result = new String[d.size()];
    for (int i = 0; d.size() > 0; ++i) {
      result[i] = d.popFirst();
    }
    return result;
  }

  // Interface and Implementation

  public interface SimpleDeque<T> {
    void addFirst(T element);
    void addLast(T element);

    T popLast();
    T popFirst();

    int size();
  }

  public static final class SimpleArrayDeque<T> implements SimpleDeque<T> {
    Object buf[] = new Object[0];
    int pos = 0;
    int size = 0;


    @Override
    public void addFirst(T element) {
      ensureEnoughSpace();

      final int newPos = (pos + buf.length - 1) % buf.length;
      this.buf[newPos] = element;
      this.pos = newPos;
      ++this.size;
    }

    @Override
    public void addLast(T element) {
      ensureEnoughSpace();

      final int p = (pos + size + buf.length) % buf.length;
      this.buf[p] = element;
      ++this.size;
    }

    @Override
    public T popLast() {
      ensureNotEmpty();
      final T result = getAndErase(size - 1);
      --this.size;

      return result;
    }

    @Override
    public T popFirst() {
      ensureNotEmpty();
      final T result = getAndErase(0);
      this.pos = (pos + 1) % buf.length;
      --this.size;

      return result;
    }

    @Override
    public int size() {
      return size;
    }

    //
    // Private
    //


    private T getAndErase(int index) {
      final int p = (index + pos) % buf.length;

      @SuppressWarnings("unchecked")
      final T result = (T) buf[p];

      buf[p] = null;

      return result;
    }

    private void ensureNotEmpty() {
      if (size == 0) {
        throw new NoSuchElementException();
      }
    }

    private void ensureEnoughSpace() {
      if (size < buf.length) {
        return;
      }

      final int newLength = Math.max(4, buf.length * 2);
      final Object newBuf[] = new Object[newLength];

      // copy one-by-one: can be optimized by using Arrays.copyOf +
      for (int i = 0; i < size; ++i) {
        newBuf[i] = buf[(i + pos) % buf.length];
      }

      this.buf = newBuf;
      this.pos = 0;
    }
  }
}
