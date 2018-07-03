package com.alexshabanov.nn.ch1.ofn;

import lombok.Value;

/**
 * Represents training data for the neural network.
 */
@Value
public final class TrainingData {
  private final double[] input;
  private final double[] output;

  public static TrainingData withInput(double... input) {
    return new TrainingData(input, new double[0]);
  }

  public TrainingData withOutput(double... output) {
    return new TrainingData(input, output);
  }
}
