package com.alexshabanov.nn.f1.util;

import java.util.Random;

/**
 * Array utilities.
 */
public final class ExtraArrays {
  private ExtraArrays() {}

  public static float[] randn(Random random, int count) {
    final float[] result = new float[count];
    for (int i = 0; i < count; ++i) {
      result[i] = (float) random.nextGaussian();
    }
    return result;
  }
}
