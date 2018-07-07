package com.alexshabanov.nn.f1.ofn;

import lombok.AllArgsConstructor;
import lombok.NonNull;

import java.util.*;
import java.util.function.Consumer;
import java.util.stream.IntStream;

import static com.alexshabanov.nn.f1.util.ExtraArrays.randn2;
import static com.alexshabanov.nn.f1.util.ExtraArrays.zeroes2;
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

  /**
   * Helper class, that holds biases for a given layer in the neural network and preceding weights,
   * connecting previous layer of the neural network with the current one, represented by biases in the
   * given segment.
   */
  static final class Segment {
    final float[] biases;
    final float[][] weights;

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
      this.biases = new float[prototype.getLayerSize()];
      this.weights = zeroes2(prototype.getPreviousLayerSize(), prototype.getLayerSize());
    }

    Segment(@NonNull float[] biases, @NonNull float[][] weights, @NonNull Segment prototype) {
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

  float[] feedforward(float[] previousLayerValues, int layerIndex, Consumer<float[]> zConsumer) {
    final int previousLayerSize = previousLayerValues.length;
    final Segment seg = this.segments.get(layerIndex);
    final int layerSize = seg.weights[0].length;

    if (seg.getPreviousLayerSize() != previousLayerSize) {
      throw new IllegalStateException("Weight matrix size=" + seg.getPreviousLayerSize() +
          " does not match previous layer size=" + previousLayerSize);
    }

    // initialize accumulated layer values with biases
    final float[] layerValues = Arrays.copyOf(seg.biases, seg.biases.length);
    assert layerValues.length == seg.getLayerSize();

    // accumulate `w * a` values in layerValues
    for (int i = 0; i < previousLayerSize; ++i) {
      final float prevNodeValue = previousLayerValues[i];
      for (int j = 0; j < layerSize; ++j) {
        layerValues[j] += prevNodeValue * seg.weights[i][j];
      }
    }

    // let callback accept z-values before transforming them using sigmoid function
    zConsumer.accept(layerValues);

    // calculate Sigmoid(Sum(W * A) + b) and put into layer values
    metadata.getSigmoid().accept(layerValues);

    return layerValues;
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

        // accumulate biases
        for (int i = 0; i < nabla.getLayerSize(); ++i) {
          nabla.biases[i] += delta.biases[i];
        }

        // accumulate weights
        for (int i = 0; i < nabla.getPreviousLayerSize(); ++i) {
          final float[] nablaWeightSlice = nabla.weights[i];
          final float[] deltaWeightSlice = delta.weights[i];
          for (int j = 0; j < nabla.getLayerSize(); ++j) {
            nablaWeightSlice[j] += deltaWeightSlice[j];
          }
        }
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

      for (int i = 0; i < nabla.getLayerSize(); ++i) {
        seg.biases[i] -= learningRate * nabla.biases[i];
      }

      for (int i = 0; i < nabla.getPreviousLayerSize(); ++i) {
        final float[] nablaWeightSlice = nabla.weights[i];
        final float[] weightSlice = seg.weights[i];
        for (int j = 0; j < nabla.getLayerSize(); ++j) {
          weightSlice[j] -= learningRate * nablaWeightSlice[j];
        }
      }
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
        this.metadata.getSigmoidPrime().accept(zPrimes);
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
        final float[][] prevWeights = seg.weights; // previous weights
        final float[] nextDelta = new float[prevWeights.length];
        for (int u = 0; u < prevWeights.length; ++u) {
          // u iterates from 0 up to current layer size
          float[] prevWeightSlice = prevWeights[u];
          float d = 0.0f;
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

      final float[][] weights = calcBackpropagatedWeights(seg, delta, activations.get(activations.size() - i - 2));

      // set nabla slice
      nablas[lastSegmentIndex - i] = new Segment(delta, weights, seg);
    }

    return new Segments(nablas);
  }

  private float[][] calcBackpropagatedWeights(Segment prototype, float[] delta, float[] prevLayerActivations) {
    // calculate matrix dot product: Delta*Transpose(A(prev))
    assert delta.length == prototype.getLayerSize();
    assert prevLayerActivations.length == prototype.getPreviousLayerSize();
    final float[][] weights = zeroes2(prototype.getPreviousLayerSize(), prototype.getLayerSize());
    for (int i = 0; i < prevLayerActivations.length; ++i) {
      for (int j = 0; j < delta.length; ++j) {
        weights[i][j] = prevLayerActivations[i] * delta[j];
      }
    }
    return weights;
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
