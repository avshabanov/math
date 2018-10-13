package com.alexshabanov.nn.f1.ofn;

import com.alexshabanov.nn.f1.cost.CostFunction;
import com.alexshabanov.nn.f1.cost.SimpleCostFunctions;
import lombok.NonNull;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Supplier;
import java.util.stream.IntStream;

/**
 * Neural network representation.
 */
public final class SimpleNeuralNetwork implements NeuralNetwork {
  final Random random;
  final Segments segments;
  final SegmentLayers layers;
  final CostFunction costFunction;

  @Override
  public Random getRandom() {
    return random;
  }

  @Override
  public Segments getSegments() {
    return this.segments;
  }

  @Override
  public SegmentLayers getSegmentLayers() {
    return this.layers;
  }

  @Override
  public CostFunction getCostFunction() {
    return this.costFunction;
  }

  public SimpleNeuralNetwork(
      @NonNull NeuralNetworkMetadata metadata,
      @NonNull CostFunction costFunction,
      @NonNull SegmentLayers layers) {
    this.random = metadata.getRandom();
    this.layers = layers;
    this.costFunction = costFunction;

    this.segments = new Segments(IntStream.range(0, layers.getCount() - 1)
        .mapToObj(i -> new Segment(
            this.random,
            layers.getLayerSize(i), layers.getLayerSize(i + 1))).toArray(Segment[]::new));
  }

  public SimpleNeuralNetwork(
      @NonNull NeuralNetworkMetadata metadata,
      @NonNull SegmentLayers layers) {
    this(metadata, SimpleCostFunctions.QUADRATIC, layers);
  }

  public int getLayerCount() {
    return this.segments.size() + 1;
  }

  float[] feedforward(float[] previousLayerValues, int layerIndex, Consumer<float[]> zConsumer) {
    final Segment seg = this.segments.get(layerIndex);
    return seg.feedforward(layers.getActivation(layerIndex), previousLayerValues, zConsumer);
  }

  float[] feedforward(float[] previousLayerValues, int layerIndex) {
    return feedforward(previousLayerValues, layerIndex, d -> {});
  }

  /**
   * Core function of neural network - pass in source values through the network and produce outputs.
   *
   * @param input Source values
   * @return Destination neuron values
   */
  @Override
  public float[] evaluate(@NonNull float[] input) {
    float[] it = input;
    for (int i = 1; i <= this.segments.size(); ++i) {
      it = feedforward(it, i - 1);
    }
    return it;
  }

  public void stochasticGradientDescent(
      @NonNull List<TrainingData> trainingSet,
      int epochs,
      int miniBatchSize,
      float learningRate,
      boolean reportEpoch) {
    stochasticGradientDescent(trainingSet, GradientDescentSettings.builder()
        .epochs(epochs)
        .miniBatchSize(miniBatchSize)
        .learningRate(learningRate)
        .reportEpoch(reportEpoch)
        .build());
  }

  public void stochasticGradientDescent(
      @NonNull List<TrainingData> trainingSet,
      @NonNull GradientDescentSettings settings) {
    // make training set mutable without affecting input argument
    final List<TrainingData> mutableTrainingSet = new ArrayList<>(trainingSet);
    final int trainingSetSize = mutableTrainingSet.size();
    final int batchCount = trainingSetSize / settings.getMiniBatchSize();
    final float weightScalingFactor = 1.0f - settings.getWeightDecay() / trainingSetSize;

    for (int j = 0; j < settings.getEpochs(); ++j) {
      long delta = System.currentTimeMillis();
      Collections.shuffle(mutableTrainingSet, this.random);

      for (int k = 0; k < batchCount; ++k) {
        final int startIndex = k * settings.getMiniBatchSize();
        final List<TrainingData> miniBatch = mutableTrainingSet.subList(startIndex,
            Math.min(startIndex + settings.getMiniBatchSize(), trainingSetSize));

        // update mini batch with parameters:
        updateMiniBatch(miniBatch, settings.getLearningRate(), weightScalingFactor);
      }

      final boolean shouldStop = settings.getStopper().shouldStop(this);
      if (settings.isReportEpoch()) {
        delta = System.currentTimeMillis() - delta;
        System.out.println("Epoch " + j + " took " + delta + "ms to complete");
        if (shouldStop) {
          System.out.println(" [stopping here]");
        }
      }

      if (shouldStop) {
        return;
      }
    }
  }

  private Segments calculateNablas(List<TrainingData> miniBatch) {
    final Segments nablas = Segments.createPrototype(this.segments);

    // run minibatches
    for (final TrainingData trainingData : miniBatch) {
      // invoke backpropagation algorithm to populate 'delta nablas' that will be collected in the actual nabla
      // which is then will be used to adjust weights and biases in the network
      final Segments deltaNablas = this.backprop(trainingData.getInput(), trainingData.getOutput());
      for (int segmentIndex = 0; segmentIndex < nablas.size(); ++segmentIndex) {
        final Segment nabla = nablas.get(segmentIndex);
        final Segment delta = deltaNablas.get(segmentIndex);

        nabla.add(delta);
      }
    }

    return nablas;
  }

  private void updateMiniBatch(List<TrainingData> miniBatch, float eta, float weightScalingFactor) {
    final Segments nablas = calculateNablas(miniBatch);

    // once nabla is known, adjust actual weights and biases
    final float learningRate = eta / miniBatch.size();
    for (int segmentIndex = 0; segmentIndex < nablas.size(); ++segmentIndex) {
      final Segment nabla = nablas.get(segmentIndex);
      final Segment seg = this.segments.get(segmentIndex);
      seg.scaleSub(nabla, learningRate, weightScalingFactor);
    }
  }

  private Segments backprop(float[] x, float[] y) {
    float[] activation = x;
    final List<float[]> activations = new ArrayList<>(getLayerCount());
    activations.add(activation);

    // Collect computed Z-values across all layers
    final List<float[]> zValueSet = new ArrayList<>(this.segments.size());

    // compute all activations and store intermediate z-vectors
    for (int i = 0; i < this.segments.size(); ++i) {
      activation = this.feedforward(activation, i, zv -> zValueSet.add(Arrays.copyOf(zv, zv.length)));
      activations.add(activation);
    }

    final Segment[] nablas = new Segment[this.segments.size()];

    // backward pass:
    float[] delta = null;
    final int lastSegmentIndex = this.segments.size() - 1;
    Segment seg = null;
    for (int i = 0; i < this.segments.size(); ++i) {
      final int layerIndex = zValueSet.size() - i - 1;
      final Supplier<float[]> zPrimeSupplier = () -> {
        // Collect computed Z' (z-prime values) across all layers
        final float[] zPrimes = zValueSet.get(layerIndex);
        this.layers.getActivationPrime(layerIndex).accept(zPrimes);
        return zPrimes;
      };

      if (i == 0) {
        // last layer: infer delta using cost derivative function
        delta = this.costFunction.delta(
            zPrimeSupplier,
            activations.get(activations.size() - 1),
            y);
      } else {
        // we need to calculate delta using previous layer's weights:
        // Delta(L-1) = Transpose(W(L-1)) * Delta(L) * S'(Z(L-1))
        delta = seg.mulTransposedWeights(delta);

        final float[] zPrimes = zPrimeSupplier.get();
        for (int j = 0; j < delta.length; ++j) {
          delta[j] = delta[j] * zPrimes[j];
        }
      }

      // find corresponding segment
      seg = this.segments.get(lastSegmentIndex - i);

      // set nabla slice
      nablas[lastSegmentIndex - i] = seg.backpropagate(delta, activations.get(activations.size() - i - 2));
    }

    return new Segments(nablas);
  }
}
