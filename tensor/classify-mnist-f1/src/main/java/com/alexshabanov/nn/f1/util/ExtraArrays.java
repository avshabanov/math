package com.alexshabanov.nn.f1.util;

import java.util.Random;

/**
 * Array utilities.
 */
public final class ExtraArrays {
  private ExtraArrays() {}

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
