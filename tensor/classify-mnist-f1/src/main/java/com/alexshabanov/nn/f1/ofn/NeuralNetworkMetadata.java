package com.alexshabanov.nn.f1.ofn;

import com.alexshabanov.nn.f1.activation.LogisticsFunction;
import com.alexshabanov.nn.f1.activation.SoftsignFunction;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Getter;
import lombok.NonNull;

import java.util.Random;
import java.util.function.Consumer;

/**
 * Neural network metadata
 */
@Builder(toBuilder = true)
@Getter
@AllArgsConstructor
public final class NeuralNetworkMetadata {
  private static final Consumer<float[]> DEFAULT_ACTIVATION = values -> {
    for (int i = 0; i < values.length; ++i) {
      values[i] = LogisticsFunction.call(values[i]);
    }
  };

  private static final Consumer<float[]> DEFAULT_ACTIVATION_PRIME = values -> {
    for (int i = 0; i < values.length; ++i) {
      values[i] = LogisticsFunction.callPrime(values[i]);
    }
  };


  @NonNull
  private final Random random;

  // NB: changing activation requires to change activationPrime as well
  @Builder.Default
  @NonNull
  private final Consumer<float[]> activation = DEFAULT_ACTIVATION;

  // NB: changing activationPrime requires to change activation as well
  @Builder.Default
  @NonNull
  private final Consumer<float[]> activationPrime = DEFAULT_ACTIVATION_PRIME;

  @Builder.Default
  private final float activationMinValue = 0; // minimum value of the activation function

  @Builder.Default
  private final float activationMaxValue = 1; // maximum value of the activation function

  // alias to minimum value of the activation function plus certain delta
  public float min(float delta) {
    return this.activationMinValue + delta;
  }

  // alias to max value of the activation function minus certain delta
  public float max(float delta) {
    return this.activationMaxValue - delta;
  }

  // alias to minimum value of the activation function
  public float min() {
    return min(0);
  }

  // alias to max value of the activation function
  public float max() {
    return max(0);
  }

  public NeuralNetworkMetadata withLogisticsFunction() {
    return this.toBuilder()
        .activation(DEFAULT_ACTIVATION)
        .activationPrime(DEFAULT_ACTIVATION_PRIME)
        .activationMinValue(0.0f)
        .activationMaxValue(1.0f)
        .build();
  }

  public NeuralNetworkMetadata withSoftsignFunction() {
    return this.toBuilder()
        .activation(values -> {
          for (int i = 0; i < values.length; ++i) {
            values[i] = SoftsignFunction.call(values[i]);
          }
        })
        .activationPrime(values -> {
          for (int i = 0; i < values.length; ++i) {
            values[i] = SoftsignFunction.callPrime(values[i]);
          }
        })
        .activationMinValue(-1.0f)
        .activationMaxValue(1.0f)
        .build();
  }
}
