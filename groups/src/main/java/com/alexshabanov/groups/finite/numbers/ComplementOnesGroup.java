package com.alexshabanov.groups.finite.numbers;

import com.alexshabanov.groups.finite.FiniteGroup;
import com.google.common.collect.ImmutableList;
import lombok.NonNull;

import java.util.List;

/**
 * A group, comprised of {-1, 1} elements and multiplication operation.
 */
public class ComplementOnesGroup implements FiniteGroup<Integer> {
  public static final ComplementOnesGroup INSTANCE = new ComplementOnesGroup();

  @Override public Integer getIdentity() { return 1; }
  @Override public @NonNull List<Integer> getElements() { return ImmutableList.of(-1, 1); }
  @Override public Integer mul(@NonNull Integer left, @NonNull Integer right) { return left * right; }

  @Override public String toString() { return "{-1, 1}"; }
}
