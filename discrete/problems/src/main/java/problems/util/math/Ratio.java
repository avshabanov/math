package problems.util.math;

import java.util.Objects;

/**
 * Represents rational number without the loss of precision within integer value bounds.
 */
public final class Ratio extends Number implements Comparable<Ratio> {
  private static final long serialVersionUID = -1002448824652078779L;

  public static final Ratio ZERO = new Ratio(0, 1);

  public static final Ratio ONE = new Ratio(1, 1);

  private final int numerator;
  private final int denominator;

  private Ratio(int numerator, int denominator) {
    this.numerator = numerator;
    this.denominator = denominator;
  }

  public static Ratio of(int numerator, int denominator) {
    if (numerator == 0) {
      return ZERO;
    }

    if (denominator == 0) {
      throw new ArithmeticException("Zero-value denominator is not allowed");
    }

    if (numerator == denominator) {
      return ONE;
    }

    final int g = gcd(numerator, denominator);
    numerator = numerator / g;
    denominator = denominator / g;
    return new Ratio(numerator, denominator);
  }

  public static Ratio fromInteger(int n) {
    return of(n, 1);
  }

  public Ratio mul(Ratio other) {
    return of(numerator * other.numerator,
        denominator * other.denominator);
  }

  public Ratio div(Ratio other) {
    return of(numerator * other.denominator,
        denominator * other.numerator);
  }

  public Ratio add(Ratio other) {
    return of(numerator * other.denominator + other.numerator * denominator,
        denominator * other.denominator);
  }

  public Ratio sub(Ratio other) {
    return new Ratio(numerator * other.denominator - other.numerator * denominator,
        denominator * other.denominator);
  }

  @Override
  public int compareTo(Ratio o) {
    final long self = this.numerator * o.denominator;
    final long other = this.denominator * o.numerator;
    return Long.compare(self, other);
  }

  @Override
  public int intValue() {
    return numerator / denominator;
  }

  @Override
  public long longValue() {
    return intValue();
  }

  @Override
  public float floatValue() {
    return ((float) numerator) / denominator;
  }

  @Override
  public double doubleValue() {
    return ((double) numerator) / denominator;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof Ratio)) return false;
    Ratio ratio = (Ratio) o;
    return numerator == ratio.numerator &&
        denominator == ratio.denominator;
  }

  @Override
  public int hashCode() {
    return Objects.hash(numerator, denominator);
  }

  @Override
  public String toString() {
    if (denominator == 1) {
      return Integer.toString(numerator);
    }
    return Integer.toString(numerator) + '/' + Integer.toString(denominator);
  }

  static int gcd(int a, int b) {
    //return BigInteger.valueOf(a).gcd(BigInteger.valueOf(b)).intValueExact();
    for (int t; b != 0; a = b, b = t % b) {
      t = a;
    }
    return a;
  }
}
