package com.alexshabanov.nn.f1.ofn;

import com.alexshabanov.nn.f1.activation.LogisticsFunction;
import com.alexshabanov.nn.f1.cost.CostFunction;
import com.alexshabanov.nn.f1.cost.SimpleCostFunctions;
import com.alexshabanov.nn.f1.util.FloatToFloatFunction;
import lombok.Builder;
import lombok.NonNull;
import org.junit.Ignore;
import org.junit.Test;

import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * Tests for toy neuron.
 */
public final class ToyNeuronTest {

  @Ignore
  @Test
  public void shouldNotIncreaseError() {
    // Given:
    final SingleNeuronNetwork n = networkBuilderWithDefaults()
        .w(0.6f).b(0.9f)
        .build();
    final float input = 1.0f;
    final float desiredOutput = 0.0f;

    // When:
    float y = n.evaluate(input);
    n.sgd(input, desiredOutput, 0.18f);
    float y2 = n.evaluate(input);

    // Then:
    assertTrue(y2 < y);
  }

  /**
   * How to plot:
   * Capture output to '/tmp/a.dat'
   *
   * Run gnuplot then type:
   * <code>
   *   set term png
   *   set output "/tmp/a.png"
   *   plot "/tmp/a.dat" using 1:2 title 'Cost'
   * </code>
   */
  @Test
  public void shouldPerformSGDUsingLogisticsFunctionAndGoodStartingValues() {
    // Given:
    final SingleNeuronNetwork n = networkBuilderWithDefaults()
        .w(0.6f).b(0.9f)
        .build();
    final float input = 1.0f;
    final float desiredOutput = 0.0f;

    // When:
    float y = n.evaluate(input);

    // Then:
    assertNotEquals(y, desiredOutput, 0.01f);

    runSgd(300, 0.15f, n, input, desiredOutput);
  }

  @Test
  public void shouldPerformSGDWithBadBiasesUsingLogisticsFunction() {
    // Given:
    final SingleNeuronNetwork n = networkBuilderWithDefaults()
        .w(2f).b(2f)
        .build();
    final float input = 1.0f;
    final float desiredOutput = 0.0f;

    // When:
    // ...

    // Then:
    runSgd(301, 0.15001f, n, input, desiredOutput);
  }

  private static void runSgd(int epochs, float learningRate, SingleNeuronNetwork n, float input, float desiredOutput) {
    System.out.printf("# For x=%.2f, y=%.2f%n", input, desiredOutput);
    System.out.println("# Iteration\tCost\tActivation\tBias\tWeight");

    for (int i = 0; i < epochs; ++i) {
      System.out.printf("%8d\t", i);
      n.sgd(input, desiredOutput, learningRate);
      System.out.println();
    }
  }

  private static SingleNeuronNetwork.SingleNeuronNetworkBuilder networkBuilderWithDefaults() {
    return SingleNeuronNetwork.builder()
        .cost(SimpleCostFunctions.QUADRATIC)
        .activation(LogisticsFunction::call)
        .activationPrime(LogisticsFunction::callPrime);
  }

  @Builder(toBuilder = true)
  private static final class SingleNeuronNetwork {

    private float w;

    private float b;

    @NonNull
    private FloatToFloatFunction activation;

    @NonNull
    private FloatToFloatFunction activationPrime;

    @NonNull
    private CostFunction cost;

    float evaluate(float x) {
      return activation.applyUnboxed(z(x));
    }

    // light-weight stochastic gradient descent
    void sgd(float x, float y, float learningRate) {
      // cost function - calc quadratic diff
      final float zv = z(x);

      // last neuron's activation
      final float av = activation.applyUnboxed(zv);

      // find cost (only to output it later)
      final float costVal = cost.call(new float[]{av}, new float[]{y})[0];

      // find C'(a)
      final float costPrimeVal = cost.callDerivative(new float[]{av}, new float[]{y})[0];

      // apply delta to find cost function
      float d = costPrimeVal * activationPrime.applyUnboxed(zv);

      // calculate nablas
      //noinspection UnnecessaryLocalVariable
      final float nb = d;
      final float nw = d * av;

      // update bias and weight
      b += nb * learningRate;
      w += nw * learningRate;

      // output new values:
      System.out.print(String.format("%.4f\t%.4f\t%.4f\t%.4f", costVal, av, b, w));
    }

    private float z(float a) {
      return b + w * a;
    }
  }
}
