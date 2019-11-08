package com.alexshabanov.groups.finite;

import com.alexshabanov.groups.exceptions.NonGroupException;
import com.alexshabanov.groups.utils.MoreStrings;
import com.google.common.collect.ImmutableSet;
import lombok.experimental.UtilityClass;

import java.io.IOException;
import java.util.List;
import java.util.Set;

/**
 * Utilities for finite groups.
 */
@UtilityClass public class FiniteGroups {

  public static <TElement> void visualize(
      Appendable target,
      FiniteGroup<TElement> group
  ) throws IOException {
    final List<TElement> elements = group.getElements();
    final int count = elements.size();
    final int maxWidth = elements.stream().map(e -> e.toString().length()).reduce(1, Math::max);
    final int cellSize = maxWidth + 2 /* 1 left padding + 1 right padding */;

    // header
    for (int i = 0; i <= count; ++i) {
      if (i == 0) {
        MoreStrings.append(target, ' ', cellSize);
      } else {
        MoreStrings.padded(target, elements.get(i - 1), cellSize);
      }

      if (i < count) {
        target.append('|');
      }
    }
    target.append('\n');

    // rows
    for (TElement left : elements) {
      // separator
      MoreStrings.append(target, '-', (cellSize + 1) * (count + 1)).append('\n');
      MoreStrings.padded(target, left, cellSize);
      // columns
      for (TElement right : elements) {
        target.append('|');
        final TElement result = group.mul(left, right);
        MoreStrings.padded(target, result, cellSize);
      }
      target.append('\n');
    }

    target.append("E=").append(group.getIdentity().toString()).append('\n');
  }

  /**
   * Verifies that group axioms (invariants) are actually met.
   * Time complexity: O(N^3).
   *
   * @param group Group to verify invariants for
   * @param <TElement> Type of the group elements
   */
  public static <TElement> void ensureValid(FiniteGroup<TElement> group) {
    final List<TElement> elements = group.getElements();
    final Set<TElement> elementSet = ImmutableSet.copyOf(elements);
    if (elements.size() != elementSet.size()) {
      // technically it IS allowed, but we weed out these for simplicity
      throw new NonGroupException("Group contains duplicate elements: " + elements);
    }

    final TElement id = group.getIdentity();
    if (!elementSet.contains(id)) {
      throw new NonGroupException("Identity element " + id + " does not belong to a group of " + elements);
    }

    for (final TElement left : elements) {
      // Ensure Identity invariant:
      final TElement idProduct = group.mul(left, id);
      if (!idProduct.equals(left)) {
        throw new NonGroupException("Identity violation: " + left + " * " + id + " produces " + idProduct);
        // NB: id * left is verified as part of associativity check
      }

      boolean inverseElementExists = false;
      for (final TElement right : elements) {
        // Ensure Closure invariant:
        final TElement product = group.mul(left, right);
        if (!elementSet.contains(product)) {
          throw new NonGroupException("Closure violation: " + left + " * " + right + " produces " + product +
              " which is not a part of group elements " + elements);
        }

        if (product.equals(id)) {
          inverseElementExists = true;
        }

        // Ensure Associativity invariant:
        for (final TElement other : elements) {
          final TElement product1 = group.mul(group.mul(left, right), other);
          final TElement product2 = group.mul(left, group.mul(right, other));
          if (!product1.equals(product2)) {
            throw new NonGroupException("Associativity violation: " + left + " * " + right + " * " + other +
                " produces distinct products " + product1 + " and " + product2 + " depending on the order of operation");
          }
        }
      }

      if (!inverseElementExists) {
        throw new NonGroupException("Inverse element violation: " + left +
            " does not have inverse counterpart out of " + elements);
      }
    }
  }
}
