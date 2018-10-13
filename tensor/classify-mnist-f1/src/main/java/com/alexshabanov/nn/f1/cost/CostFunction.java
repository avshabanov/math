package com.alexshabanov.nn.f1.cost;

import java.util.function.Consumer;
import java.util.function.Supplier;

/**
 * Cost function prototype.
 */
public interface CostFunction {

  float[] call(float[] neuronOutput, float[] expectedOutput);

  float[] callDerivative(float[] neuronOutput, float[] expectedOutput);

  default float[] delta(
      Supplier<float[]> zValuePrimeSupplier,
      float[] neuronOutput,
      float[] expectedOutput) {
    // Generic delta function
    final float[] delta = this.callDerivative(neuronOutput, expectedOutput);
    final float[] zPrimes = zValuePrimeSupplier.get();
    for (int i = 0; i < zPrimes.length; ++i) {
      delta[i] *= zPrimes[i];
    }
    return delta;
  }
}
