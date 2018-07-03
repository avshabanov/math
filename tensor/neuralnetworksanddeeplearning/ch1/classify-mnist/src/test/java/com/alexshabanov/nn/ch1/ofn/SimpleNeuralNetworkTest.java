package com.alexshabanov.nn.ch1.ofn;

import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.DoubleStream;

import static org.junit.Assert.assertEquals;

/**
 * Tests for {@link SimpleNeuralNetwork} class.
 */
public final class SimpleNeuralNetworkTest {
  private final Random random = new Random(100L);

  @Test
  public void shouldBeAbleToUseIdentityNetwork() {
    final SimpleNeuralNetwork n = new SimpleNeuralNetwork(random, new int[]{2, 3, 1});
    assertEquals(2, n.segments.size());

    final double[] result = n.evaluate(new double[] {0.01, 0.9});
    assertEquals(1, result.length);
  }

  @Test
  public void shouldBeAbleToLearnNandOperation() {
    System.out.println("nand operation learn");

    final List<TrainingData> trainingSet = Arrays.asList(
        TrainingData.withInput(0, 0).withOutput(1),
        TrainingData.withInput(1, 0).withOutput(1),
        TrainingData.withInput(0, 1).withOutput(1),
        TrainingData.withInput(1, 1).withOutput(0)
    );
    final SimpleNeuralNetwork n = new SimpleNeuralNetwork(random, new int[]{2, 1});
    n.stochasticGradientDescent(trainingSet, 1000, 4, 3.0);

    for (final TrainingData trainingData : trainingSet) {
      final double[] output = n.evaluate(trainingData.getInput());

      // now check, that real output difference is in sync with the outputs:
      final double[] expected = trainingData.getOutput();
      assertEquals(expected[0], output[0], 0.1);

      System.out.println("input=" + doublesToString(trainingData.getInput()) + ", output=" + doublesToString(output));
    }
  }

  @Test
  public void shouldBeAbleToLearnStairsPattern() {
    final List<TrainingData> trainingSet = new ArrayList<>();
    int stairCount = 0;
    while (trainingSet.size() < 1000) {
      final double d0 = random.nextInt(90) / 100.0;
      final double d1 = random.nextInt(90) / 100.0;
      final double d2 = random.nextInt(90) / 100.0;
      final double d3 = random.nextInt(90) / 100.0;
      if ((d0 < 0.25 && d1 >= 0.25 && d2 >= 0.25 && d3 >= 0.25) ||
          (d0 >= 0.25 && d1 < 0.25 && d2 >= 0.25 && d3 >= 0.25)) {
        ++stairCount;
        trainingSet.add(new TrainingData(new double[]{d0, d1, d2, d3}, new double[]{1.0}));
      }

      if (stairCount < trainingSet.size() / 3) {
        // make sure at least third of training set is filled up
        continue;
      }

      // add negative training set
      trainingSet.add(new TrainingData(new double[]{d0, d1, d2, d3}, new double[]{0.0}));
    }

    System.out.println("stairs pattern recognition");

    final SimpleNeuralNetwork n = new SimpleNeuralNetwork(random, new int[]{4, 2, 2, 1});
    n.stochasticGradientDescent(trainingSet, 3000, 500, 3.0);

    final double[] rightStairOutput = n.evaluate(new double[]{0.0, 0.9, 0.9, 0.9});
    System.out.println("rightStairOutput output=" + doublesToString(rightStairOutput));

    final double[] leftStairOutput = n.evaluate(new double[]{0.9, 0.12, 0.85, 0.78});
    System.out.println("leftStairOutput output=" + doublesToString(leftStairOutput));

    final double[] nonStairOutput1 = n.evaluate(new double[]{0.65, 0.9, 0.29, 0.1});
    System.out.println("nonStairOutput1=" + doublesToString(nonStairOutput1));

    final double[] nonStairOutput2 = n.evaluate(new double[]{0.84, 0.68, 0.05, 0.1});
    System.out.println("nonStairOutput2=" + doublesToString(nonStairOutput2));
  }

  private static String doublesToString(double[] arr) {
    return DoubleStream.of(arr).mapToObj(d -> String.format("%.2f", d)).collect(Collectors.toList()).toString();
  }
}
