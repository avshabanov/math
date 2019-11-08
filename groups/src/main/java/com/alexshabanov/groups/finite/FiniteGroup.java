package com.alexshabanov.groups.finite;

import lombok.NonNull;

import java.util.List;

/**
 * Abstraction for representing finite groups.
 * Each element <strong>MUST</strong> have proper equals function defined.
 */
public interface FiniteGroup<TElement> {
  @NonNull TElement getIdentity();
  @NonNull List<TElement> getElements();
  @NonNull TElement mul(@NonNull TElement left, @NonNull TElement right);
}
