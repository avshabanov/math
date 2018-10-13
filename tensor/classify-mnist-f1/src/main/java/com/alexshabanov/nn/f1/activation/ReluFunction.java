package com.alexshabanov.nn.f1.activation;

/**
 * ReLU (Reduced Linear Unit) is an activation function that looks as follows:
 * <code>
 *   f(x) = max(0, x)
 * </code>
 * Its derivative is 0 for x less than or equal to 0 and 1 for x greater than zero.
 */
public final class ReluFunction {
  private ReluFunction() {}

  public static float call(float x) {
    return x > 0 ? x : 0;
  }

  public static float callPrime(float x) {
    return x > 0 ? 1 : 0;
  }
}
