package com.alexshabanov.groups.finite.numbers;

import com.alexshabanov.groups.finite.FiniteGroup;
import lombok.NonNull;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Defines finite group on top of the integer number <code>[from, to)</code>.
 */
public abstract class IntRangeGroup implements FiniteGroup<Integer> {
  private final int from;
  private final int to;

  public IntRangeGroup(int from, int to) {
    if (from >= to) {
      throw new IllegalArgumentException("Illegal range: lower bound is greater or equal to the upper bound " +
          toString());
    }

    this.from = from;
    this.to = to;

    if (getIdentity() < from || getIdentity() >= to) {
      throw new IllegalArgumentException("Illegal range for identity element " + getIdentity() +
          ": it is not within " + toString());
    }
  }

  @Override public @NonNull List<Integer> getElements() {
    return IntStream.range(from, to).boxed().collect(Collectors.toList());
  }

  @Override
  public String toString() {
    return "[" + from + ", " + to + ")";
  }
}
