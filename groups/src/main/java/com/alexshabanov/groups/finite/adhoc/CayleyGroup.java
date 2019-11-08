package com.alexshabanov.groups.finite.adhoc;

import com.alexshabanov.groups.finite.FiniteGroup;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Defines Cayley group for elements {1, -1, i, -i} with identity element 1 and standard multiplication.
 */
public final class CayleyGroup implements FiniteGroup<CayleyGroup.Element> {
  public static final CayleyGroup INSTANCE = new CayleyGroup();

  private CayleyGroup() {}

  /** An element of the Cayley group. */
  public enum Element {
    ONE(1, 0),
    MINUS_ONE(-1, 0),
    I(0, 1),
    MINUS_I(0, -1);

    private final int real;
    private final int imaginary;

    private static final int FOLD_MULTIPLIER = 2/* Element.values().length / 2 or count of distinct reals == imaginaries */;
    private static final Map<Integer, Element> FOLD_MAP = Arrays.stream(Element.values())
        .collect(Collectors.toMap(Element::fold, i -> i));

    Element(int real, int imaginary) {
      assert real == 1 || real == -1 || real == 0;
      assert imaginary == 1 || imaginary == -1 || imaginary == 0;
      assert (Math.abs(real) == 1 && imaginary == 0) || (Math.abs(imaginary) == 1 && real == 0);
      this.real = real;
      this.imaginary = imaginary;
    }

    @Override
    public String toString() {
      return real != 0 ? Integer.toString(real) : (imaginary < 0 ? "-i" : "i");
    }

    /**
     * @return Result of folding this element into 1D set (simplistic Hilbert's curve).
     */
    private int fold() {
      return fold(this.real, this.imaginary);
    }

    private static int fold(int real, int imaginary) {
      return real * FOLD_MULTIPLIER + imaginary;
    }

    private static Element unfold(int key) {
      final Element result = FOLD_MAP.get(key);
      if (result == null) {
        throw new IllegalStateException("Unable to unfold the key=" + key);
      }
      return result;
    }

    public Element mul(Element other) {
      return unfold(fold(
          this.real * other.real - this.imaginary * other.imaginary,
          this.imaginary * other.real + this.real * other.imaginary
      ));
    }
  }

  @Override public Element getIdentity() {
    return Element.ONE;
  }

  @Override public List<Element> getElements() {
    return Arrays.asList(Element.values());
  }

  @Override public Element mul(Element left, Element right) {
    return left.mul(right);
  }
}
