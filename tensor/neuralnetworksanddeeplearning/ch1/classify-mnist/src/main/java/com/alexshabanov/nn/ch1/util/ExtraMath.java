package com.alexshabanov.nn.ch1.util;

import java.util.Random;
import java.util.concurrent.ThreadLocalRandom;

/**
 * Neural network utilities.
 */
public final class ExtraMath {
  private ExtraMath() {}

  public static double sigmoid(double x) {
    return 1.0 / (1.0 + Math.exp(-x));
  }

  // first derivative from sigmoid function
  public static double sigmoidPrime(double x) {
    final double v = sigmoid(x);
    return v * (1 - v);
  }

  public static double[][] randn2(Random random, int d0, int d1) {
    final double[][] result = new double[d0][];
    for (int i = 0; i < d0; ++i) {
      final double[] slice = new double[d1];
      result[i] = slice;

      for (int j = 0; j < d1; ++j) {
        slice[j] = random.nextGaussian();
      }
    }
    return result;
  }

  public static double[][] zeroes2(int d0, int d1) {
    final double[][] result = new double[d0][];
    for (int i = 0; i < d0; ++i) {
      result[i] = new double[d1];
    }
    return result;
  }
}
