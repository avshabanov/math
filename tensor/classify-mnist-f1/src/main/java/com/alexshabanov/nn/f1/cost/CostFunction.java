package com.alexshabanov.nn.f1.cost;

/**
 * Cost function prototype.
 */
public interface CostFunction {
  float call(float neuronOutput, float expectedOutput);
}
