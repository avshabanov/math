package com.alexshabanov.nn.f1.activation;

/**
 * Utility class, encapsulating reverse absolute value function and its first derivative:
 * <pre>
 *   f(x) = x / (1 + abs(x)):
 *   for x>=0 => f'(x) = (x/(1+x))' = (1 - 1/(1+x))' =
 *      = (1+x)'* (-1) * 1/(1+x)^2 = 1/(1+x)^2.
 *   for x < 0 -> f'(x) = (x / (1-x))' = (1/(1-x) - 1)' = (1-x)' * (-1) * 1/(1-x)^2 = 1/(1-x)^2
 * </pre>
 *
 * See also https://en.wikipedia.org/wiki/Activation_function
 */
public final class SoftsignFunction {
  private SoftsignFunction() {}

  public static float call(float x) {
    return x / (1 + Math.abs(x));
  }

  public static float callPrime(float x) {
    final float v = 1 + Math.abs(x);
    return 1.0f / (v * v);
  }
}
