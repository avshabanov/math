package com.alexshabanov.groups.finite.adhoc;

import com.alexshabanov.groups.finite.FiniteGroup;
import com.google.common.collect.ImmutableMap;
import lombok.NonNull;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

/**
 * The symmetry group of the square (D4).
 */
public final class SquareSymmetryGroup implements FiniteGroup<SquareSymmetryGroup.Element> {
  public static final SquareSymmetryGroup INSTANCE = new SquareSymmetryGroup();

  public enum Element {
    /** Keep as it is */
    ID,

    /** Rotation by pi/2, clockwise */
    R1,

    /** Rotation by pi, clockwise */
    R2,

    /** Rotation by 3*pi/2, clockwise */
    R3,

    /** Vertical reflection */
    FV,

    /** Horizontal reflection */
    FH,

    /** Diagonal reflection */
    FD,

    /** Counter diagonal reflection */
    FC
  }

  private static final Map<Element, Map<Element, Element>> PACKED_MUL_MAP = ImmutableMap.<Element, Map<Element, Element>>builder()
      .put(Element.R1, ImmutableMap.<Element, Element>builder()
          .put(Element.R1, Element.R2)
          .put(Element.R2, Element.R3)
          .put(Element.R3, Element.ID)
          .put(Element.FV, Element.FC)
          .put(Element.FH, Element.FD)
          .put(Element.FD, Element.FV)
          .put(Element.FC, Element.FH)
          .build())
      .put(Element.R2, ImmutableMap.<Element, Element>builder()
          .put(Element.R1, Element.R3)
          .put(Element.R2, Element.ID)
          .put(Element.R3, Element.R1)
          .put(Element.FV, Element.FH)
          .put(Element.FH, Element.FV)
          .put(Element.FD, Element.FC)
          .put(Element.FC, Element.FD)
          .build())
      .put(Element.R3, ImmutableMap.<Element, Element>builder()
          .put(Element.R1, Element.ID)
          .put(Element.R2, Element.R1)
          .put(Element.R3, Element.R2)
          .put(Element.FV, Element.FD)
          .put(Element.FH, Element.FC)
          .put(Element.FD, Element.FH)
          .put(Element.FC, Element.FV)
          .build())
      .put(Element.FV, ImmutableMap.<Element, Element>builder()
          .put(Element.R1, Element.FD)
          .put(Element.R2, Element.FH)
          .put(Element.R3, Element.FC)
          .put(Element.FV, Element.ID)
          .put(Element.FH, Element.R2)
          .put(Element.FD, Element.R1)
          .put(Element.FC, Element.R3)
          .build())
      .put(Element.FH, ImmutableMap.<Element, Element>builder()
          .put(Element.R1, Element.FC)
          .put(Element.R2, Element.FV)
          .put(Element.R3, Element.FD)
          .put(Element.FV, Element.R2)
          .put(Element.FH, Element.ID)
          .put(Element.FD, Element.R3)
          .put(Element.FC, Element.R1)
          .build())
      .put(Element.FD, ImmutableMap.<Element, Element>builder()
          .put(Element.R1, Element.FH)
          .put(Element.R2, Element.FC)
          .put(Element.R3, Element.FV)
          .put(Element.FV, Element.R3)
          .put(Element.FH, Element.R1)
          .put(Element.FD, Element.ID)
          .put(Element.FC, Element.R2)
          .build())
      .put(Element.FC, ImmutableMap.<Element, Element>builder()
          .put(Element.R1, Element.FV)
          .put(Element.R2, Element.FD)
          .put(Element.R3, Element.FH)
          .put(Element.FV, Element.R1)
          .put(Element.FH, Element.R3)
          .put(Element.FD, Element.R2)
          .put(Element.FC, Element.ID)
          .build())
      .build();

  @Override public Element getIdentity() {
    return Element.ID;
  }

  @Override public @NonNull List<Element> getElements() {
    return Arrays.asList(Element.values());
  }

  @Override public Element mul(@NonNull Element left, @NonNull Element right) {
    if (left == Element.ID) {
      return right;
    }
    if (right == Element.ID) {
      return left;
    }

    final Element result = PACKED_MUL_MAP.get(left).get(right);
    if (result == null) {
      throw new IllegalStateException("Packed operation map is missing an entry for left=" + left +
          " and right=" + right);
    }
    return result;
  }
}
