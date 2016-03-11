package support;

import java.util.Arrays;

/**
 * Provides helpers for operating with single linked lists.
 */
public abstract class SingleLinkedListSupport {

  public static class Node<T> {
    T value;
    Node<T> next;

    public T getValue() {
      return value;
    }

    public void setValue(T value) {
      this.value = value;
    }

    public Node<T> getNext() {
      return next;
    }

    public void setNext(Node<T> next) {
      this.next = next;
    }

    @Override
    public String toString() {
      final StringBuilder sb = new StringBuilder();
      sb.append('[');
      boolean next = false;
      for (Node<T> n = this; n != null; n = n.getNext()) {
        if (next) {
          sb.append(", ");
        }
        next = true;
        sb.append(n.getValue());
      }
      sb.append(']');
      return sb.toString();
    }
  }

  public static <T> Node<T> newNode(T value, Node<T> next) {
    final Node<T> result = new Node<>();
    result.setValue(value);
    result.setNext(next);
    return result;
  }

  public static <T> Node<T> fromArray(T[] values) {
    Node<T> result = null;
    Node<T> it = null;
    for (final T value : values) {
      if (it == null) {
        result = new Node<>();
        result.setValue(value);
        it = result;
      } else {
        final Node<T> n = new Node<>();
        n.setValue(value);
        it.setNext(n);
        it = n;
      }
    }
    return result;
  }

  public static <T> int getLength(Node<T> n) {
    int i = 0;
    for (; n != null; n = n.getNext()) {
      ++i;
    }
    return i;
  }

  public static <T> T[] toArray(Node<T> n, T[] src) {
    final int length = getLength(n);
    if (length != src.length) {
      src = Arrays.copyOf(src, length);
    }

    for (int i = 0; i < length; ++i) {
      src[i] = n.getValue();
      n = n.getNext();
    }

    return src;
  }
}
