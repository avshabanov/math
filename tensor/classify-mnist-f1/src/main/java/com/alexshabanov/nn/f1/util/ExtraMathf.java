package com.alexshabanov.nn.f1.util;

import java.util.Random;

/**
 * Neural network utilities.
 */
public final class ExtraMathf {
  private ExtraMathf() {}

  public static float sigmoid(float x) {
    // TODO: Use alternative to sigmoid: f(x) = x / (1 + abs(x))
    return 1.0f / (1.0f + (float) Math.exp(-x));
  }

  // first derivative from sigmoid function
  public static float sigmoidPrime(float x) {
    final float v = sigmoid(x);
    return v * (1.0f - v);
  }

  public static float[][] randn2(Random random, int d0, int d1) {
    final float[][] result = new float[d0][];
    for (int i = 0; i < d0; ++i) {
      final float[] slice = new float[d1];
      result[i] = slice;

      for (int j = 0; j < d1; ++j) {
        slice[j] = (float) random.nextGaussian();
      }
    }
    return result;
  }

  public static float[][] zeroes2(int d0, int d1) {
    final float[][] result = new float[d0][];
    for (int i = 0; i < d0; ++i) {
      result[i] = new float[d1];
    }
    return result;
  }
}
