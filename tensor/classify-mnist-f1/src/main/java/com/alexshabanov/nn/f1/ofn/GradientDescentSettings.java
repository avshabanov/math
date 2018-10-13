package com.alexshabanov.nn.f1.ofn;

import lombok.Builder;
import lombok.Value;

/**
 * Stores settings to gradient descent operation.
 */
@Value
@Builder(toBuilder = true)
public final class GradientDescentSettings {
  private final int epochs;

  @Builder.Default
  private final int miniBatchSize = 1;

  @Builder.Default
  private final float learningRate = 1.0f;

  @Builder.Default
  private final float weightDecay = 0.0f;

  private final boolean reportEpoch;

  @Builder.Default
  private final Stopper stopper = SimpleStoppers.NEVER;

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
