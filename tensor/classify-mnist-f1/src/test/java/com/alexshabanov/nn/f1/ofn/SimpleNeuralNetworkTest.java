package com.alexshabanov.nn.f1.ofn;

import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import static com.alexshabanov.nn.f1.ClassifyMainF1.floatsToString;
import static org.junit.Assert.assertEquals;

/**
 * Tests for {@link SimpleNeuralNetwork} class.
 */
public final class SimpleNeuralNetworkTest {
  private final NeuralNetworkMetadata metadata = NeuralNetworkMetadata.getClassicDefault().toBuilder()
      .random(new Random(100L))
      .build();

  @Test
  public void shouldBeAbleToUseIdentityNetwork() {
    final SimpleNeuralNetwork n = new SimpleNeuralNetwork(metadata, new int[]{2, 3, 1});
    assertEquals(2, n.segments.size());

    final float[] result = n.evaluate(new float[] {0.01f, 0.9f});
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
    final SimpleNeuralNetwork n = new SimpleNeuralNetwork(metadata, new int[]{2, 1});
    n.stochasticGradientDescent(trainingSet, 1000, 4, 3.0f, false);

    for (final TrainingData trainingData : trainingSet) {
      final float[] output = n.evaluate(trainingData.getInput());

      // now check, that real output difference is in sync with the outputs:
      final float[] expected = trainingData.getOutput();
      assertEquals(expected[0], output[0], 0.1);

      System.out.println("input=" + floatsToString(trainingData.getInput()) + ", output=" + floatsToString(output));
    }
  }

  // Returns random two-digit float number between 0 and 1, e.g. 0.65, 0.89, etc.
  private float[] randFloats(int size, int granularity) {
    final float[] r = new float[size];
    for (int i = 0; i < size; ++i) {
      r[i] = metadata.getRandom().nextInt(granularity) / ((float) granularity);
    }
    return r;
  }

  @Test
  public void shouldBeAbleToLearnStairsPattern() {
    final List<TrainingData> trainingSet = new ArrayList<>();
    int stairCount = 0;
    while (trainingSet.size() < 5000) {
      final float[] d = randFloats(4, 1000);
      if ((d[0] < 0.1 && d[1] >= 0.1 && d[2] >= 0.1 && d[3] >= 0.1) ||
          (d[0] >= 0.1 && d[1] < 0.1 && d[2] >= 0.1 && d[3] >= 0.1)) {
        ++stairCount;
        trainingSet.add(new TrainingData(d, new float[]{1.0f}));
      }

      if (stairCount < trainingSet.size() / 3) {
        // make sure at least third of training set is filled up
        continue;
      }

      // add negative training set
      trainingSet.add(new TrainingData(d, new float[]{0.0f}));
    }

    System.out.println("stairs pattern recognition");

    final SimpleNeuralNetwork n = new SimpleNeuralNetwork(metadata, new int[]{4, 4, 2, 1});
    n.stochasticGradientDescent(trainingSet, 50, 30, 5.0f, false);

    final float[] rightStairOutput = n.evaluate(new float[]{0.01f, 0.98f, 0.85f, 0.78f});
    System.out.println("rightStairOutput=" + floatsToString(rightStairOutput));

    final float[] rightStairOutput2 = n.evaluate(new float[]{0.0f, 1.0f, 1.0f, 1.0f});
    System.out.println("rightStairOutput2=" + floatsToString(rightStairOutput2));

    final float[] leftStairOutput = n.evaluate(new float[]{0.9f, 0.01f, 0.85f, 0.78f});
    System.out.println("leftStairOutput=" + floatsToString(leftStairOutput));

    final float[] nonStairOutput1 = n.evaluate(new float[]{0.65f, 0.9f, 0.29f, 0.01f});
    System.out.println("nonStairOutput1=" + floatsToString(nonStairOutput1));

    final float[] nonStairOutput2 = n.evaluate(new float[]{0.84f, 0.68f, 0.05f, 0.01f});
    System.out.println("nonStairOutput2=" + floatsToString(nonStairOutput2));
  }
}
