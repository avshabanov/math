package com.alexshabanov.nn.f1.cost;

/**
 * Calculates quadratic cost function
 */
public enum SimpleCostFunctions implements CostFunction {

  /**
   * A function that looks as follows:
   * <code>C(y) = (y - a)^2  /  2</code>
   */
  QUADRATIC {
    @Override
    public float[] call(float[] neuronOutput, float[] expectedOutput) {
      assert neuronOutput.length == expectedOutput.length;
      final float[] result = new float[expectedOutput.length];
      for (int i = 0; i < expectedOutput.length; ++i) {
        final float v = (expectedOutput[i] - neuronOutput[i]);
        result[i] = v * v / 2.0f;
      }
      return result;
    }

    @Override
    public float[] callDerivative(float[] neuronOutput, float[] expectedOutput) {
      assert neuronOutput.length == expectedOutput.length;
      final float[] result = new float[expectedOutput.length];
      for (int i = 0; i < expectedOutput.length; ++i) {
        result[i] = neuronOutput[i] - expectedOutput[i];
      }
      return result;
    }
  }
}
