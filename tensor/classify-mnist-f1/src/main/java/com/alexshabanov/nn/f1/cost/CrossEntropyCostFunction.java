package com.alexshabanov.nn.f1.cost;

/**
 * Calculates cross-entropy cost function, or
 * <code>
 *   C = -\frac{1}{n} \sum_x \left[y \ln a + (1-y ) \ln (1-a) \right]
 * </code>
 */
public final class CrossEntropyCostFunction {
  private CrossEntropyCostFunction() {}

  public static float call(float neuronOutput, float expectedOutput) {
    final float v = (float) (expectedOutput * Math.log(neuronOutput) + (1.0 - expectedOutput) * Math.log(1.0 - neuronOutput));
    return Float.isNaN(v) ? 0.0f : v;
  }
}
