package support;

import java.util.Arrays;
import java.util.Objects;

/**
 * Provides helpers for operating with single linked lists.
 */
public abstract class SingleLinkedListSupport {

  public static class Node<T> {
    private static final int MAX_TO_STRING = 32;

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
      int cap = 0;
      for (Node<T> n = this; n != null && cap < MAX_TO_STRING; n = n.getNext(), ++cap) {
        if (next) {
          sb.append(", ");
        }
        next = true;
        n.stringifyNode(sb);
      }
      if (cap == MAX_TO_STRING) {
        sb.append("...");
      }

      sb.append(']');
      return sb.toString();
    }

    protected void stringifyNode(StringBuilder target) {
      target.append(getValue());
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof Node)) return false;

      Node<?> node = (Node<?>) o;

      if (!Objects.equals(getValue(), node.getValue())) {
        return false;
      }

      return Objects.equals(node.getNext(), getNext());
    }

    @Override
    public int hashCode() {
      int result = value != null ? value.hashCode() : 0;
      result = 31 * result + (next != null ? next.hashCode() : 0);
      return result;
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
