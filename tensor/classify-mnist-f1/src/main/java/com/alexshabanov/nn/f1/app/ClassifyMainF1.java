package com.alexshabanov.nn.f1.app;

import com.alexshabanov.nn.f1.ofn.*;
import com.alexshabanov.nn.f1.util.MnistLoader;

import java.io.File;
import java.util.List;
import java.util.concurrent.ThreadLocalRandom;

import static com.alexshabanov.nn.f1.util.ExtraArrays.floatsToString;

/**
 * Main entry point.
 */
public final class ClassifyMainF1 {

  public static void main(String[] args) throws Exception {
    if (args.length < 1) {
      throw new IllegalArgumentException("Unexpected arg count: first arg should be a path to gzipped MNIST data." +
          " See also http://yann.lecun.com/exdb/mnist/");
    }
    final String folder = args[0];

    if (args.length > 1 && "-debugLoader".equals(args[1])) {
      final MnistLoader.IdxImages images = MnistLoader.load(
          folder + File.separatorChar + "t10k-images-idx3-ubyte.gz",
          folder + File.separatorChar + "t10k-labels-idx1-ubyte.gz"
      );
      images.dump(10);
      return;
    }

    final MnistLoader.IdxImages images = MnistLoader.load(
        folder + File.separatorChar + "train-images-idx3-ubyte.gz",
        folder + File.separatorChar + "train-labels-idx1-ubyte.gz"
    );
    final List<TrainingData> trainingDataSet = images.toTrainingData();

    final SimpleNeuralNetwork neuralNetwork;
    float eta = 3.0f;
    NeuralNetworkMetadata metadata = NeuralNetworkMetadata.builder().random(ThreadLocalRandom.current()).build();
    if (args.length > 1 && "-useSoftsignOnly".equals(args[1])) {
      neuralNetwork = new SimpleNeuralNetwork(metadata,
          SegmentLayers.of(NeuronActivation.softsign(), 784).add(30).add(10));
    } else if (args.length > 1 && "-useSigmoidOnly".equals(args[1])) {
      neuralNetwork = new SimpleNeuralNetwork(metadata,
          SegmentLayers.of(NeuronActivation.sigmoid(), 784).add(30).add(10));
    } else {
      eta = 1.0f;
      neuralNetwork = new SimpleNeuralNetwork(metadata,
          SegmentLayers.of(NeuronActivation.relu(), 784)
              .add(30)
              .add(NeuronActivation.sigmoid(), 10));
      // TODO: add early stop capability
    }

    neuralNetwork.stochasticGradientDescent(trainingDataSet, 30, 10, eta, true);

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
    System.out.printf("Match quality: %.2f percent(s)%n",
        (100.0 * (trainingDataSet.size() - mismatches)) / trainingDataSet.size());
  }
}
