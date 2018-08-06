package com.alexshabanov.nn.f1.cost;

/**
 * Calculates quadratic cost function
 */
public final class QuadraticCostFunction {
  private QuadraticCostFunction() {}

  // C(y) = (y - a)^2  /  2
  public static float call(float neuronOutput, float expectedOutput) {
    final float v = (expectedOutput - neuronOutput);
    return  v * v / 2.0f;
  }

  public static float callPrime(float neuronOutput, float expectedOutput) {
    return expectedOutput - neuronOutput;
  }
}
