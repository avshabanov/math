package com.alexshabanov.nn.ch1.ofn;

import com.alexshabanov.nn.ch1.util.ExtraMath;
import lombok.AllArgsConstructor;
import lombok.NonNull;

import java.util.*;
import java.util.function.Consumer;
import java.util.stream.DoubleStream;
import java.util.stream.IntStream;

import static com.alexshabanov.nn.ch1.util.ExtraMath.*;
import static java.util.Objects.requireNonNull;

/**
 * Neural network representation.
 */
public class SimpleNeuralNetwork {
  final Segments segments;
  final Random random;

  public SimpleNeuralNetwork(@NonNull Random random, @NonNull int[] sizes) {
    this.random = requireNonNull(random);
    this.segments = new Segments(IntStream.range(0, sizes.length - 1)
        .mapToObj(i -> new Segment(random, sizes[i], sizes[i + 1])).toArray(Segment[]::new));
  }

  public int getLayerCount() {
    return this.segments.size() + 1;
  }

  /**
   * Helper class, that holds biases for a given layer in the neural network and preceding weights,
   * connecting previous layer of the neural network with the current one, represented by biases in the
   * given segment.
   */
  static final class Segment {
    final double[] biases;
    final double[][] weights;

    Segment(@NonNull Random random, int previousLayerSize, int layerSize) {
      if (previousLayerSize <= 0) {
        throw new IllegalArgumentException("previousLayerSize");
      }

      if (layerSize <= 0) {
        throw new IllegalArgumentException("layerSize");
      }
      this.biases = randn2(random, 1, layerSize)[0];
      this.weights = randn2(random, previousLayerSize, layerSize);
    }

    Segment(@NonNull Segment prototype) {
      this.biases = new double[prototype.getLayerSize()];
      this.weights = zeroes2(prototype.getPreviousLayerSize(), prototype.getLayerSize());
    }

    Segment(@NonNull double[] biases, @NonNull double[][] weights, @NonNull Segment prototype) {
      this.biases = biases;
      this.weights = weights;

      if (this.biases.length != prototype.getLayerSize()) {
        throw new IllegalArgumentException("Unexpected biases size=" + this.biases.length +
            ", expected=" + prototype.getLayerSize());
      }

      if (this.weights.length != prototype.getPreviousLayerSize()) {
        throw new IllegalArgumentException("Unexpected weights 1d size=" + this.weights.length +
            ", expected=" + prototype.getPreviousLayerSize());
      }

      if (this.weights[0].length != prototype.getLayerSize()) {
        throw new IllegalArgumentException("Unexpected weights 2d size=" + this.weights[0].length +
            ", expected=" + prototype.getLayerSize());
      }
    }

    int getLayerSize() {
      assert biases.length == weights[0].length;
      return biases.length;
    }

    int getPreviousLayerSize() {
      return weights.length;
    }
  }

  @AllArgsConstructor
  static final class Segments {
    private final Segment[] segments;

    public int size() {
      return this.segments.length;
    }

    public Segment get(int index) {
      return this.segments[index];
    }

    // Creates new segments, where all biases and weights are initialized to zeroes
    public static Segments createPrototype(@NonNull Segments template) {
      return new Segments(Arrays.stream(template.segments).map(Segment::new).toArray(Segment[]::new));
    }
  }

  double[] feedforward(double[] previousLayerValues, int layerIndex, Consumer<double[]> zConsumer) {
    final int previousLayerSize = previousLayerValues.length;
    final Segment seg = this.segments.get(layerIndex);
    final int layerSize = seg.weights[0].length;

    if (seg.getPreviousLayerSize() != previousLayerSize) {
      throw new IllegalStateException("Weight matrix size=" + seg.getPreviousLayerSize() +
          " does not match previous layer size=" + previousLayerSize);
    }

    // initialize accumulated layer values with biases
    final double[] layerValues = Arrays.copyOf(seg.biases, seg.biases.length);
    assert layerValues.length == seg.getLayerSize();

    // accumulate `w * a` values in layerValues
    for (int i = 0; i < previousLayerSize; ++i) {
      final double prevNodeValue = previousLayerValues[i];
      for (int j = 0; j < layerSize; ++j) {
        layerValues[j] += prevNodeValue * seg.weights[i][j];
      }
    }

    // let callback accept z-values before transforming them using sigmoid function
    zConsumer.accept(layerValues);

    // calculate Sigmoid(Sum(W * A) + b) and put into layer values
    for (int j = 0; j < layerSize; ++j) {
      layerValues[j] = sigmoid(layerValues[j]);
    }

    return layerValues;
  }

  double[] feedforward(double[] previousLayerValues, int layerIndex) {
    return feedforward(previousLayerValues, layerIndex, d -> {});
  }

  /**
   * Core function of neural network - pass in source values through the network and produce outputs.
   *
   * @param input Source values
   * @return Destination neuron values
   */
  public double[] evaluate(@NonNull double[] input) {
    double[] it = input;
    for (int i = 1; i <= this.segments.size(); ++i) {
      it = feedforward(it, i - 1);
    }
    return it;
  }

  public void stochasticGradientDescent(
      @NonNull List<TrainingData> trainingSet,
      int epochs,
      int miniBatchSize,
      double eta,
      boolean reportEpoch) {
    // make training set mutable without affecting input argument
    final List<TrainingData> mutableTrainingSet = new ArrayList<>(trainingSet);
    final int trainingSetSize = mutableTrainingSet.size();
    final int batchCount = trainingSetSize / miniBatchSize;

    for (int j = 0; j < epochs; ++j) {
      long delta = System.currentTimeMillis();
      Collections.shuffle(mutableTrainingSet, this.random);

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

  private void updateMiniBatch(List<TrainingData> miniBatch, double eta) {
    final Segments nablas = Segments.createPrototype(this.segments);

    // run minibatches
    for (final TrainingData trainingData : miniBatch) {
      // invoke backpropagation algorithm to populate 'delta nablas' that will be collected in the actual nabla
      // which is then will be used to adjust weights and biases in the network
      final Segments deltaNablas = this.backprop(trainingData.getInput(), trainingData.getOutput());
      for (int segmentIndex = 0; segmentIndex < nablas.size(); ++segmentIndex) {
        final Segment nabla = nablas.get(segmentIndex);
        final Segment delta = deltaNablas.get(segmentIndex);

        // accumulate biases
        for (int i = 0; i < nabla.getLayerSize(); ++i) {
          nabla.biases[i] += delta.biases[i];
        }

        // accumulate weights
        for (int i = 0; i < nabla.getPreviousLayerSize(); ++i) {
          final double[] nablaWeightSlice = nabla.weights[i];
          final double[] deltaWeightSlice = delta.weights[i];
          for (int j = 0; j < nabla.getLayerSize(); ++j) {
            nablaWeightSlice[j] += deltaWeightSlice[j];
          }
        }
      }
    }

    // once nabla is known, adjust actual weights and biases
    final double learningRate = eta / miniBatch.size();
    for (int segmentIndex = 0; segmentIndex < nablas.size(); ++segmentIndex) {
      final Segment nabla = nablas.get(segmentIndex);
      final Segment seg = this.segments.get(segmentIndex);

      for (int i = 0; i < nabla.getLayerSize(); ++i) {
        seg.biases[i] -= learningRate * nabla.biases[i];
      }

      for (int i = 0; i < nabla.getPreviousLayerSize(); ++i) {
        final double[] nablaWeightSlice = nabla.weights[i];
        final double[] weightSlice = seg.weights[i];
        for (int j = 0; j < nabla.getLayerSize(); ++j) {
          weightSlice[j] -= learningRate * nablaWeightSlice[j];
        }
      }
    }
  }

  private Segments backprop(double[] x, double[] y) {
    double[] activation = x;
    final List<double[]> activations = new ArrayList<>(getLayerCount());
    activations.add(activation);

    // Collect computed Z' (z-prime values) across all layers
    final List<double[]> zPrimeValueSet = new ArrayList<>(this.segments.size());

    // compute all activations and store intermediate z-vectors
    for (int i = 0; i < this.segments.size(); ++i) {
      activation = this.feedforward(activation, i, zValues ->
          zPrimeValueSet.add(DoubleStream.of(zValues).map(ExtraMath::sigmoidPrime).toArray()));
      activations.add(activation);
    }

    final Segment[] nablas = new Segment[this.segments.size()];

    // backward pass:
    double[] delta = null;
    final int lastSegmentIndex = this.segments.size() - 1;
    Segment seg = null;
    for (int i = 0; i < this.segments.size(); ++i) {
      final double[] zPrimes = zPrimeValueSet.get(zPrimeValueSet.size() - i - 1);

      if (i == 0) {
        // last layer: infer delta using cost derivative function
        delta = this.costDerivative(activations.get(activations.size() - 1), y);
      } else {
        // TODO: fixme - this needs to be optimized further
        // we need to calculate delta using previous layer's weights:
        // Delta(L-1) = Transpose(W(L-1)) * Delta(L) * S'(Z(L-1))
        final double[][] prevWeights = seg.weights; // previous weights
        final double[] nextDelta = new double[prevWeights.length];
        for (int u = 0; u < prevWeights.length; ++u) {
          // u iterates from 0 up to current layer size
          double[] prevWeightSlice = prevWeights[u];
          double d = 0.0;
          for (int v = 0; v < prevWeightSlice.length; ++v) {
            d += delta[v] * prevWeightSlice[v];
          }
          nextDelta[u] = d;
        }

        // update delta array
        delta = nextDelta;
      }

      // find corresponding segment
      seg = this.segments.get(lastSegmentIndex - i);

      // here: finalize computing delta as C'(An, Y) * S'(Zn), where An is last activation layer values and
      // Zn - is last activation layer's z-values
      for (int j = 0; j < delta.length; ++j) {
        delta[j] = delta[j] * zPrimes[j];
      }

      final double[][] weights = calcBackpropagatedWeights(seg, delta, activations.get(activations.size() - i - 2));

      // set nabla slice
      nablas[lastSegmentIndex - i] = new Segment(delta, weights, seg);
    }

    return new Segments(nablas);
  }

  private double[][] calcBackpropagatedWeights(Segment prototype, double[] delta, double[] prevLayerActivations) {
    // calculate matrix dot product: Delta*Transpose(A(prev))
    assert delta.length == prototype.getLayerSize();
    assert prevLayerActivations.length == prototype.getPreviousLayerSize();
    final double[][] weights = zeroes2(prototype.getPreviousLayerSize(), prototype.getLayerSize());
    for (int i = 0; i < prevLayerActivations.length; ++i) {
      for (int j = 0; j < delta.length; ++j) {
        weights[i][j] = prevLayerActivations[i] * delta[j];
      }
    }
    return weights;
  }

  private double[] costDerivative(double[] outputActivations, double[] y) {
    assert outputActivations.length == y.length;
    final double[] result = new double[outputActivations.length];
    for (int i = 0; i < outputActivations.length; ++i) {
      result[i] = outputActivations[i] - y[i];
    }
    return result;
  }
}
