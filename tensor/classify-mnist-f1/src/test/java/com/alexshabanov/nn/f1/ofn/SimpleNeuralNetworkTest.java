package com.alexshabanov.nn.f1.ofn;

import lombok.AccessLevel;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Value;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.internal.ArrayComparisonFailure;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import static com.alexshabanov.nn.f1.ClassifyMainF1.floatsToString;
import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;

/**
 * Tests for {@link SimpleNeuralNetwork} class.
 */
public final class SimpleNeuralNetworkTest {
  private final NeuralNetworkMetadata defaultMetadata = NeuralNetworkMetadata.builder()
      .random(new Random(100L))
      .build();

  private List<TrainingData> stairsPattern;

  @Before
  public void init() {
    stairsPattern = stairsPattern != null ? stairsPattern : createStairsPatternTrainingSet();
  }

  private List<TrainingData> createStairsPatternTrainingSet() {
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
    return trainingSet;
  }

  @Test
  public void shouldBeAbleToUseIdentityNetwork() {
    final SimpleNeuralNetwork n = new SimpleNeuralNetwork(defaultMetadata, new int[]{2, 3, 1});
    assertEquals(2, n.segments.size());

    final float[] result = n.evaluate(new float[] {0.01f, 0.9f});
    assertEquals(1, result.length);
  }

  private static void testNandOperationLearn(NeuralNetworkMetadata m, LearnSettings s) {
    final float e1 = 0.0001f;
    final float e2 = 0.001f;
    final List<TrainingData> trainingSet = Arrays.asList(
        TrainingData.withInput(m.min(), m.min()).withOutput(m.max()),
        TrainingData.withInput(m.max(), m.min()).withOutput(m.max()),
        TrainingData.withInput(m.min(), m.max()).withOutput(m.max()),
        TrainingData.withInput(m.max(), m.max()).withOutput(m.min()),

        TrainingData.withInput(m.min(e1), m.min(e1)).withOutput(m.max(e1)),
        TrainingData.withInput(m.max(e1), m.min(e1)).withOutput(m.max(e1)),
        TrainingData.withInput(m.min(e1), m.max(e1)).withOutput(m.max(e1)),
        TrainingData.withInput(m.max(e1), m.max(e1)).withOutput(m.min(e1)),

        TrainingData.withInput(m.min(e2), m.min(e2)).withOutput(m.max(e2)),
        TrainingData.withInput(m.max(e2), m.min(e2)).withOutput(m.max(e2)),
        TrainingData.withInput(m.min(e2), m.max(e2)).withOutput(m.max(e2)),
        TrainingData.withInput(m.max(e2), m.max(e2)).withOutput(m.min(e2))
    );

    final SimpleNeuralNetwork n = new SimpleNeuralNetwork(m, new int[]{2, 1});
    //n.stochasticGradientDescent(trainingSet, 30, 4, 30.0f, false);
    n.stochasticGradientDescent(trainingSet, s.getEpochs(), s.getMiniBatchSize(), s.getEta(), false);

    for (final TrainingData trainingData : trainingSet) {
      final float[] output = n.evaluate(trainingData.getInput());

      // now check, that real output difference is in sync with the outputs:
      final float[] expected = trainingData.getOutput();
      assertArrayEquals("Expected=" + floatsToString(expected) + ", actual=" + floatsToString(output),
          expected, output, s.getExpectedResultSensitivity());

      System.out.println("input=" + floatsToString(trainingData.getInput()) + ", output=" + floatsToString(output));
    }
  }

  @Test
  public void shouldBeAbleToLearnNandOperation() {
    testNandOperationLearn(defaultMetadata, LearnSettings.getDefault());
  }

  @Ignore
  @Test
  public void shouldBeAbleToLearnNandOperationUsingGaussFunction() {
    // TODO: impl
  }

  @Test
  public void shouldBeAbleToLearnNandOperationUsingSoftsignFunction() {
    testNandOperationLearn(
        defaultMetadata.withSoftsignFunction(),
        LearnSettings.getDefault().toBuilder()
            .epochs(40)
            .build()
    );
  }

  @Test
  public void shouldBeAbleToLearnStairsPattern() {
    final List<TrainingData> trainingSet = this.stairsPattern;

    System.out.println("stairs pattern recognition");

    final SimpleNeuralNetwork n = new SimpleNeuralNetwork(defaultMetadata, new int[]{4, 4, 2, 1});
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

  @Test
  public void shouldClassifyCircleUsingLogisticsActivationFunction() {
    testCircleClassification(defaultMetadata, LearnSettings.getDefault().toBuilder()
        .epochs(4000)
        .miniBatchSize(300)
        .eta(30.0f)
        .build(),
        0 /*make sure that we fail on any inconsistency*/);
  }

  @Test
  public void shouldClassifyCircleUsingSoftsignActivationFunction() {
    testCircleClassification(defaultMetadata.withSoftsignFunction(), LearnSettings.getDefault().toBuilder()
        .epochs(4000)
        .miniBatchSize(300)
        .eta(30.0f)
        .build(),
        3/*allow that many inconsistencies*/);
  }

  private static void testCircleClassification(NeuralNetworkMetadata m, LearnSettings s, int allowedNumberOfErrors) {
    // problem: there is a set of dots inside the circle with radius 2. All the other dots are located outside that
    // radius. Output: two nodes, first node outputs one if dot is within the circle, the other - if it is outside.
    // see also: https://playground.tensorflow.org/#activation=sigmoid&batchSize=10&dataset=circle&regDataset=reg-plane&learningRate=0.03&regularizationRate=0&noise=0&networkShape=4,2&seed=0.59072&showTestData=false&discretize=false&percTrainData=50&x=true&y=true&xTimesY=false&xSquared=false&ySquared=false&cosX=false&sinX=false&cosY=false&sinY=false&collectStats=false&problem=classification&initZero=false&hideText=false

    final Random random = m.getRandom();
    final int trainingSize = 1000;
    final List<TrainingData> trainingSet = new ArrayList<>(trainingSize);
    final float[] blueOutput = new float[] { m.max(), m.min() };
    final float[] redOutput = new float[] { m.min(), m.max() };
    for (int i = 0; i < trainingSize; ++i) {
      final float angle = random.nextFloat() * 2.0f * (float) Math.PI;
      final float radius;
      final float[] output;
      if ((i & 1) == 0) {
        radius = random.nextFloat() * 2.0f;
        output = blueOutput;
      } else {
        // keep 2.5 gap
        radius = 2.5f + random.nextFloat() * 2;
        output = redOutput;
      }

      final float[] input = new float[] {
          radius * (float) Math.cos(angle),
          radius * (float) Math.sin(angle)
      };

      trainingSet.add(TrainingData.withInput(input).withOutput(output));
    }

    final SimpleNeuralNetwork n = new SimpleNeuralNetwork(m, new int[]{2, 4, 2});

    n.stochasticGradientDescent(trainingSet, s.getEpochs(), s.getMiniBatchSize(), s.getEta(), false);

    int mismatchCount = 0;
    for (int i = 0; i < trainingSet.size(); ++i) {
      final TrainingData trainingData = trainingSet.get(i);

      final float[] output = n.evaluate(trainingData.getInput());

      // now check, that real output difference is in sync with the outputs:
      final float[] expected = trainingData.getOutput();

      try {
        assertArrayEquals("Expected=" + floatsToString(expected) + ", actual=" + floatsToString(output) +
                " at i=" + i,
            expected, output, s.getExpectedResultSensitivity());
      } catch (ArrayComparisonFailure e) {
        ++mismatchCount;
        if (mismatchCount > allowedNumberOfErrors) {
          throw e;
        }
      }
    }

    if (mismatchCount > 0) {
      System.out.println("Mismatches found: " + mismatchCount);
    }
  }

  //
  // Private
  //

  // Returns random two-digit float number between 0 and 1, e.g. 0.65, 0.89, etc.
  private float[] randFloats(int size, int granularity) {
    final float[] r = new float[size];
    for (int i = 0; i < size; ++i) {
      r[i] = defaultMetadata.getRandom().nextInt(granularity) / ((float) granularity);
    }
    return r;
  }



  @Builder(toBuilder = true)
  @Value
  @AllArgsConstructor(access = AccessLevel.PRIVATE)
  static final class LearnSettings {
    private final int epochs;
    private final int miniBatchSize;
    private final float eta;
    private final float expectedResultSensitivity;



    public static LearnSettings getDefault() {
      return LearnSettings.builder()
          .epochs(30)
          .miniBatchSize(4)
          .eta(30.0f)
          .expectedResultSensitivity(0.15f)
          .build();
    }
  }
}
