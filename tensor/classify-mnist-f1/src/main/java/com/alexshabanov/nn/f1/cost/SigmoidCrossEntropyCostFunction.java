package com.alexshabanov.nn.f1.cost;

import java.util.function.Supplier;

/**
 * Calculates cross-entropy cost function, or
 * <code>
 *   C = -\frac{1}{n} \sum_x \left[y \ln a + (1-y ) \ln (1-a) \right]
 * </code>
 */
public class SigmoidCrossEntropyCostFunction implements CostFunction {

  @Override
  public float[] call(float[] neuronOutput, float[] expectedOutput) {
    assert neuronOutput.length == expectedOutput.length;
    final float[] result = new float[expectedOutput.length];
    for (int i = 0; i < expectedOutput.length; ++i) {
      result[i] = crossEntropy(neuronOutput[i], expectedOutput[i]);
    }
    return result;
  }

  @Override
  public float[] callDerivative(float[] neuronOutput, float[] expectedOutput) {
    // TODO: implement
    // Usually you don't want to call this method
    throw new UnsupportedOperationException();
  }

  @Override
  public float[] delta(Supplier<float[]> zValuePrimeSupplier, float[] neuronOutput, float[] expectedOutput) {
    assert neuronOutput.length == expectedOutput.length;
    final float[] result = new float[expectedOutput.length];
    for (int i = 0; i < expectedOutput.length; ++i) {
      result[i] = neuronOutput[i] - expectedOutput[i];
    }
    return result;
  }

  public static float crossEntropy(float neuronOutput, float expectedOutput) {
    final float v = (float) ((-expectedOutput * Math.log(neuronOutput)) -
        (1.0 - expectedOutput) * Math.log(1.0 - neuronOutput));

    if (v == Float.POSITIVE_INFINITY) {
      // return big enough number
      return 1e+10f;
    } else if (v == Float.NEGATIVE_INFINITY) {
      // return small enough number
      return -1e+10f;
    }

    if (Float.isNaN(v)) {
      return 0.0f;
    }

    return v;
  }
}
