package com.alexshabanov.nn.f1.app;

import com.alexshabanov.nn.f1.cost.CostFunction;
import com.alexshabanov.nn.f1.cost.SigmoidCrossEntropyCostFunction;
import com.alexshabanov.nn.f1.cost.SimpleCostFunctions;
import com.alexshabanov.nn.f1.ofn.*;
import com.alexshabanov.nn.f1.util.MnistLoader;
import lombok.AllArgsConstructor;

import java.io.File;
import java.util.List;
import java.util.concurrent.ThreadLocalRandom;

import static com.alexshabanov.nn.f1.util.ExtraArrays.floatsToString;

/**
 * Runs experimental network.
 */
public class RunMnistExperimentMain {

  public static void main(String[] args) throws Exception {
    if (args.length < 1) {
      throw new IllegalArgumentException("Unexpected arg count: first arg should be a path to gzipped MNIST data." +
          " See also http://yann.lecun.com/exdb/mnist/");
    }
    final String folder = args[0];

    long deltaMillis = System.currentTimeMillis();

    // load main data chunk
    final MnistLoader.IdxImages images = MnistLoader.load(
        folder + File.separatorChar + "train-images-idx3-ubyte.gz",
        folder + File.separatorChar + "train-labels-idx1-ubyte.gz"
    );
    final List<TrainingData> trainingDataSet = images.toTrainingData();

    // load training data chunk
    final MnistLoader.IdxImages testImages = MnistLoader.load(
        folder + File.separatorChar + "t10k-images-idx3-ubyte.gz",
        folder + File.separatorChar + "t10k-labels-idx1-ubyte.gz"
    );
    final List<TrainingData> testTrainingDataSet = testImages.toTrainingData();

    // complete time measurement
    deltaMillis = System.currentTimeMillis() - deltaMillis;
    System.out.println("Input data loaded in " + deltaMillis + "msec");

    final SegmentLayers layers = SegmentLayers
        //.of(NeuronActivation.relu(), 784)
        .of(NeuronActivation.sigmoid(), 784)
        //.add(100)
        .add(30)
        .add(NeuronActivation.sigmoid()/*last layer is always sigmoid for normalization*/, 10);

    final CostFunction costFunction = new SigmoidCrossEntropyCostFunction();
    //final CostFunction costFunction = SimpleCostFunctions.QUADRATIC;

    final SimpleNeuralNetwork neuralNetwork = new SimpleNeuralNetwork(
        NeuralNetworkMetadata.builder().random(ThreadLocalRandom.current()).build(),
        costFunction,
        layers);

    final GradientDescentSettings.Stopper stopper = new EarlyStopper(testTrainingDataSet);
    // do dry run simulation
    stopper.shouldStop(neuralNetwork);

    System.out.println("Running epochs...");

    neuralNetwork.stochasticGradientDescent(
        trainingDataSet,
        GradientDescentSettings.builder()
            .epochs(30)
            .miniBatchSize(10)
            .learningRate(0.3f)
            //.weightDecay(20.0f)
            .reportEpoch(true)
            .stopper(stopper)
            .build());

    if (args.length < 10) {
      return;
    }

    // now test the network using first few images
    System.out.println("Test network:");
    for (int i = 0; i < Math.min(10, trainingDataSet.size()); ++i) {
      final TrainingData td = trainingDataSet.get(i);
      final float[] output = neuralNetwork.evaluate(td.getInput());
      System.out.println("Image #" + i + ", expected label: " + images.getLabels()[i]);
      System.out.println("\tGot output=" + floatsToString(output) + ", expected=" + floatsToString(td.getOutput()));
    }

    int mismatches = 0;
    for (final TrainingData td : trainingDataSet) {
      final float[] output = neuralNetwork.evaluate(td.getInput());
      for (int j = 0; j < output.length; ++j) {
        if (Math.abs(output[j] - td.getOutput()[j]) > 0.4) {
          ++mismatches;
          break;
        }
      }
    }
    System.out.println(String.format("Match quality: %.2f percent(s)",
        (100.0 * (trainingDataSet.size() - mismatches)) / trainingDataSet.size()));
  }

  @AllArgsConstructor
  private static final class EarlyStopper implements GradientDescentSettings.Stopper {
    private final List<TrainingData> testDataSet;

    @Override
    public boolean shouldStop(NeuralNetwork network) {
      float accumulatedCost = 0.0f;
      int mismatches = 0;
      for (TrainingData trainingData : testDataSet) {
        // perform evaluation
        final float[] output = network.evaluate(trainingData.getInput());
        final float[] cost = network.getCostFunction().call(output, trainingData.getOutput());

        // calculate accrued cost
        for (float costUnit : cost) {
          accumulatedCost += costUnit;
        }

        // also calculate mismatches
        for (int j = 0; j < output.length; ++j) {
          final float out = output[j];
          if (Float.isNaN(out) || Math.abs(out - trainingData.getOutput()[j]) > 0.4) {
            ++mismatches;
            break;
          }
        }
      }

      final float matchQuality = (100.0f * (testDataSet.size() - mismatches)) / testDataSet.size();

      accumulatedCost /= testDataSet.size();
      System.out.printf("[Epoch Evaluator] Accumulated cost: %.4f, match quality: %.1f percents\n",
          accumulatedCost, matchQuality);

      return false;
    }
  }
}
