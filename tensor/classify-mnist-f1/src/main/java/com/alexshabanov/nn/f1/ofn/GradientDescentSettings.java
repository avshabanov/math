package com.alexshabanov.nn.f1.ofn;

import lombok.Builder;
import lombok.Value;

/**
 * Stores settings to gradient descent operation.
 */
@Value
@Builder(toBuilder = true)
public class GradientDescentSettings {
  int epochs;

  @Builder.Default
  int miniBatchSize = 1;

  @Builder.Default
  float learningRate = 1.0f;

  @Builder.Default
  float weightDecay = 0.0f;

  boolean reportEpoch;

  @Builder.Default
  Stopper stopper = SimpleStoppers.NEVER;

  public interface Stopper {
    boolean shouldStop(NeuralNetwork context);
  }

  public enum SimpleStoppers implements Stopper {
    NEVER{
      @Override
      public boolean shouldStop(NeuralNetwork n) {
        return false;
      }
    }
  }
}
