package util;

import java.util.List;

/**
 * An interface to the simplest lock free stack.
 */
public interface LockFreeStack<T> {

  void push(T element);

  T pop(T defaultElement);

  int size();

  List<T> toList();
}
