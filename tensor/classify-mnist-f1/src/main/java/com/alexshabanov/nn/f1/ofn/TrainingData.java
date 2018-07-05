package com.alexshabanov.nn.f1.ofn;

import lombok.Value;

/**
 * Represents training data for the neural network.
 */
@Value
public final class TrainingData {
  private final float[] input;
  private final float[] output;

  public static TrainingData withInput(float... input) {
    return new TrainingData(input, new float[0]);
  }

  public TrainingData withOutput(float... output) {
    return new TrainingData(input, output);
  }
}
