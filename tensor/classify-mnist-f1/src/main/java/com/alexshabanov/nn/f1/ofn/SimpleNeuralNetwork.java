package com.alexshabanov.nn.f1.ofn;

import lombok.NonNull;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.function.Consumer;
import java.util.stream.IntStream;

import static java.util.Objects.requireNonNull;

/**
 * Neural network representation.
 */
public class SimpleNeuralNetwork {
  final Segments segments;
  final NeuralNetworkMetadata metadata;

  public SimpleNeuralNetwork(
      @NonNull NeuralNetworkMetadata metadata,
      @NonNull int[] sizes) {
    this.metadata = requireNonNull(metadata);
    this.segments = new Segments(IntStream.range(0, sizes.length - 1)
        .mapToObj(i -> new Segment(metadata.getRandom(), sizes[i], sizes[i + 1])).toArray(Segment[]::new));
  }

  public int getLayerCount() {
    return this.segments.size() + 1;
  }

  float[] feedforward(float[] previousLayerValues, int layerIndex, Consumer<float[]> zConsumer) {
    final Segment seg = this.segments.get(layerIndex);
    return seg.feedforward(metadata, previousLayerValues, zConsumer);
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
      float eta,
      boolean reportEpoch) {
    // make training set mutable without affecting input argument
    final List<TrainingData> mutableTrainingSet = new ArrayList<>(trainingSet);
    final int trainingSetSize = mutableTrainingSet.size();
    final int batchCount = trainingSetSize / miniBatchSize;

    for (int j = 0; j < epochs; ++j) {
      long delta = System.currentTimeMillis();
      Collections.shuffle(mutableTrainingSet, this.metadata.getRandom());

      for (int k = 0; k < batchCount; ++k) {
        final int startIndex = k * miniBatchSize;
        final List<TrainingData> miniBatch = mutableTrainingSet.subList(startIndex,
            Math.min(startIndex + miniBatchSize, trainingSetSize));

        updateMiniBatch(miniBatch, eta);
      }

      if (reportEpoch) {
        delta = System.currentTimeMillis() - delta;
        System.out.println("Epoch " + j + " took " + delta + "ms to complete");
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

  private void updateMiniBatch(List<TrainingData> miniBatch, float eta) {
    final Segments nablas = calculateNablas(miniBatch);

    // once nabla is known, adjust actual weights and biases
    final float learningRate = eta / miniBatch.size();
    for (int segmentIndex = 0; segmentIndex < nablas.size(); ++segmentIndex) {
      final Segment nabla = nablas.get(segmentIndex);
      final Segment seg = this.segments.get(segmentIndex);
      seg.scaleSub(nabla, learningRate);
    }
  }

  private Segments backprop(float[] x, float[] y) {
    float[] activation = x;
    final List<float[]> activations = new ArrayList<>(getLayerCount());
    activations.add(activation);

    // Collect computed Z' (z-prime values) across all layers
    final List<float[]> zPrimeValueSet = new ArrayList<>(this.segments.size());

    // compute all activations and store intermediate z-vectors
    for (int i = 0; i < this.segments.size(); ++i) {
      activation = this.feedforward(activation, i, zValues -> {
        final float[] zPrimes = Arrays.copyOf(zValues, zValues.length);
        this.metadata.getActivationPrime().accept(zPrimes);
        zPrimeValueSet.add(zPrimes);
      });
      activations.add(activation);
    }

    final Segment[] nablas = new Segment[this.segments.size()];

    // backward pass:
    float[] delta = null;
    final int lastSegmentIndex = this.segments.size() - 1;
    Segment seg = null;
    for (int i = 0; i < this.segments.size(); ++i) {
      final float[] zPrimes = zPrimeValueSet.get(zPrimeValueSet.size() - i - 1);

      if (i == 0) {
        // last layer: infer delta using cost derivative function
        delta = this.costDerivative(activations.get(activations.size() - 1), y);
      } else {
        // TODO: fixme - this needs to be optimized further
        // we need to calculate delta using previous layer's weights:
        // Delta(L-1) = Transpose(W(L-1)) * Delta(L) * S'(Z(L-1))
        delta = seg.mulTransposedWeights(delta);
      }

      // here: finalize computing delta as C'(An, Y) * S'(Zn), where An is last activation layer values and
      // Zn - is last activation layer's z-values
      for (int j = 0; j < delta.length; ++j) {
        delta[j] = delta[j] * zPrimes[j];
      }

      // find corresponding segment
      seg = this.segments.get(lastSegmentIndex - i);

      // set nabla slice
      nablas[lastSegmentIndex - i] = seg.backpropagate(delta, activations.get(activations.size() - i - 2));
    }

    return new Segments(nablas);
  }

  private float[] costDerivative(float[] outputActivations, float[] y) {
    assert outputActivations.length == y.length;
    final float[] result = new float[outputActivations.length];
    for (int i = 0; i < outputActivations.length; ++i) {
      result[i] = outputActivations[i] - y[i];
    }
    return result;
  }
}
