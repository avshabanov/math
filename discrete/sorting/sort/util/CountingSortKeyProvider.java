package util;

/**
 * An interface, provided by user knowing how to fold input element into an integer key,
 * that should be greater or equals to zero and strictly less than provided maximum value.
 *
 * This interface exists only to support counting sort algorithms.
 *
 * @param <T> Source element
 * @author Alexander Shabanov
 */
public interface CountingSortKeyProvider<T> {
  int getMaximumValue();

  int getKey(T value);
}
