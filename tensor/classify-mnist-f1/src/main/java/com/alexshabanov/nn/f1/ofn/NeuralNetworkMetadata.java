package com.alexshabanov.nn.f1.ofn;

import com.alexshabanov.nn.f1.util.AbsInvFunction;
import com.alexshabanov.nn.f1.util.LogisticsFunction;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Getter;
import lombok.NonNull;

import java.util.Random;
import java.util.concurrent.ThreadLocalRandom;
import java.util.function.Consumer;

/**
 * Neural network metadata
 */
@Builder(toBuilder = true)
@Getter
@AllArgsConstructor
public final class NeuralNetworkMetadata {
  @NonNull
  private final Random random;

  @NonNull
  private final Consumer<float[]> sigmoid;

  @NonNull
  private final Consumer<float[]> sigmoidPrime;

  // TODO: cost derivative

  public static NeuralNetworkMetadata withLogisticsFunction() {
    return new NeuralNetworkMetadata(
        ThreadLocalRandom.current(),
        values -> {
          for (int i = 0; i < values.length; ++i) {
            values[i] = LogisticsFunction.call(values[i]);
          }
        },
        values -> {
          for (int i = 0; i < values.length; ++i) {
            values[i] = LogisticsFunction.callPrime(values[i]);
          }
        }
    );
  }

  public static NeuralNetworkMetadata withAbsInvFunction() {
    return new NeuralNetworkMetadata(
        ThreadLocalRandom.current(),
        values -> {
          for (int i = 0; i < values.length; ++i) {
            values[i] = AbsInvFunction.call(values[i]);
          }
        },
        values -> {
          for (int i = 0; i < values.length; ++i) {
            values[i] = AbsInvFunction.callPrime(values[i]);
          }
        }
    );
  }
}
