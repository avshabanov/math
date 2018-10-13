package com.alexshabanov.nn.f1.ofn;

import com.alexshabanov.nn.f1.activation.LogisticsFunction;
import com.alexshabanov.nn.f1.activation.ReluFunction;
import com.alexshabanov.nn.f1.activation.SoftsignFunction;
import lombok.AllArgsConstructor;
import lombok.Getter;

import java.util.function.Consumer;

/**
 * Represents metadata on neuron activation.
 */
@AllArgsConstructor
@Getter
public final class NeuronActivation {

  private final Consumer<float[]> activation;
  private final Consumer<float[]> activationPrime;

  public static NeuronActivation sigmoid() {
    return new NeuronActivation(
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

  public static NeuronActivation relu() {
    return new NeuronActivation(
        values -> {
          for (int i = 0; i < values.length; ++i) {
            values[i] = ReluFunction.call(values[i]);
          }
        },
        values -> {
          for (int i = 0; i < values.length; ++i) {
            values[i] = ReluFunction.callPrime(values[i]);
          }
        }
    );
  }

  public static NeuronActivation softsign() {
    return new NeuronActivation(
        values -> {
          for (int i = 0; i < values.length; ++i) {
            values[i] = SoftsignFunction.call(values[i]);
          }
        },
        values -> {
          for (int i = 0; i < values.length; ++i) {
            values[i] = SoftsignFunction.callPrime(values[i]);
          }
        }
    );
  }
}
