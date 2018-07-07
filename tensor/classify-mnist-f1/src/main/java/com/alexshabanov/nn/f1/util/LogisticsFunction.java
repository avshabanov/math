package com.alexshabanov.nn.f1.util;

/**
 * Utility class, encapsulating logistic function and it's first derivative (prime):
 * <pre>
 *   s'(x) = (1+e^(-x))' * -((1+e^(-x))^(-2)) = (-1) * e^(-x) * -((1+e^(-x))^(-2)) =
 *   = e^(-x) / (1 + e^(-x))^2 = s(x) * (e^(-x) / (1 + e^(-x))) = s(x) * (1 - s(x)).
 * </pre>
 */
public final class LogisticsFunction {
  private LogisticsFunction() {}

  public static float call(float x) {
    return 1.0f / (1.0f + (float) Math.exp(-x));
  }

  public static float callPrime(float x) {
    final float v = call(x);
    return v * (1.0f - v);
  }
}
