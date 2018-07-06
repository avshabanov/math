package com.alexshabanov.nn.f1.util;

/**
 * Encapsulates logistics function
 */
public final class LogisticsFunction {
  private LogisticsFunction() {}

  public static float call(float x) {
    // TODO: Use alternative to sigmoid: f(x) = x / (1 + abs(x))
    return 1.0f / (1.0f + (float) Math.exp(-x));
  }

  /**
   * Derivative of sigmoid function.
   *
   * @param x Value
   * @return Result
   */
  public static float callPrime(float x) {
    final float v = call(x);
    return v * (1.0f - v);
  }
}
