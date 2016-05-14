import support.SingleLinkedListSupport;

import java.util.Objects;

/**
 * Sample run:
 * <pre>
 * source=[1, 2, 3, 4, 5, 6, 7, 8], result=[1, 2, 4, 5, 7, 8]
 * source=[1, 2, 3, 4, 5, 6, 7, 8], result=[1, 4, 7]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class PeriodicDeleteExample extends SingleLinkedListSupport {

  public static void main(String[] args) {
    demo(new Integer[] { 1, 2, 3, 4, 5, 6, 7, 8 }, 2, 1);
    demo(new Integer[] { 1, 2, 3, 4, 5, 6, 7, 8 }, 1, 2);
    demo(new Integer[] { 1, 2, 3, 4, 5, 6, 7, 8 }, 0, 1);
    demo(new Integer[] { 1, 2, 3, 4, 5, 6, 7, 8 }, 1, 0);
  }

  public static void demo(Integer[] arr, int m, int n) {
    final Node<Integer> source = fromArray(arr);
    final Node<Integer> result = periodicDelete(source, m, n);
    final Node<Integer> result2 = periodicDelete2(source, m, n);
    if (!Objects.equals(result, result2)) {
      throw new AssertionError("mismatched periodic delete result for source=" + source);
    }
    System.out.println("source=" + source + ", result=" + result);
  }

  public static Node<Integer> periodicDelete(Node<Integer> list, int m, int n) {
    final Finder<Integer> finder = new Finder<>(m, n);
    return finder.find(list);
  }

  public static final class Finder<T> {
    final int retainCount;
    final int deleteCount;

    public Finder(int retainCount, int deleteCount) {
      if (retainCount < 0 || deleteCount < 0 || (retainCount == 0 && deleteCount == 0)) {
        throw new IllegalArgumentException("Illegal retainCount=" + retainCount +
            ", deleteCount=" + deleteCount);
      }

      this.retainCount = retainCount;
      this.deleteCount = deleteCount;
    }

    public Node<T> find(Node<T> source) {
      return retain(source, retainCount);
    }

    private Node<T> retain(Node<T> source, int counter) {
      if (source == null) {
        return null;
      }

      if (counter == 0) {
        return delete(source, deleteCount);
      }

      final Node<T> target = new Node<>();
      target.setValue(source.getValue());
      target.setNext(retain(source.getNext(), --counter));
      return target;
    }

    private Node<T> delete(Node<T> source, int counter) {
      if (source == null) {
        return null;
      }

      if (counter == 0) {
        return retain(source, retainCount);
      }

      return delete(source.getNext(), --counter);
    }
  }

  public static <T> Node<T> periodicDelete2(Node<T> list, int retainCount, int deleteCount) {
    if (retainCount < 0 || deleteCount < 0 || (retainCount == 0 && deleteCount == 0)) {
      throw new IllegalArgumentException("Illegal retainCount=" + retainCount +
          ", deleteCount=" + deleteCount);
    }

    Node<T> result = null;
    Node<T> it = null;

    while (list != null) {
      for (int i = 0; i < retainCount; ++i) {
        if (list == null) {
          break;
        }
        final Node<T> next = new Node<>();
        next.setValue(list.getValue());
        if (it == null) {
          it = next;
          result = it;
        } else {
          it.setNext(next);
          it = next;
        }
        list = list.getNext();
      }

      for (int i = 0; i < deleteCount; ++i) {
        if (list == null) {
          break;
        }
        list = list.getNext();
      }
    }

    return result;
  }
}
