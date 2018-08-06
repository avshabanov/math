package com.alexshabanov.nn.f1.ofn;

import lombok.NonNull;

import java.util.Arrays;
import java.util.Random;
import java.util.function.Consumer;

import static com.alexshabanov.nn.f1.util.ExtraArrays.randn;

/**
 * Helper class, that holds biases for a given layer in the neural network and preceding weights,
 * connecting previous layer of the neural network with the current one, represented by biases in the
 * given segment.
 */
public final class Segment {
  private final int previousLayerSize; // M or previous layer size
  private final int layerSize;
  private final float[] biases; // 1xN matrix, stores neuron biases, N is the current layer size
  private final float[] weights; // MxN matrix, stores neuron weight matrix, see getIndex function for indexing

  /**
   * @param w Row
   * @param h Column
   * @return Position in the weights array
   */
  private int getIndex(int w, int h) {
    assert w >= 0 && w < getPreviousLayerSize();
    assert h >= 0 && h < getLayerSize();
    return w * this.getLayerSize() + h;
  }

  public Segment(@NonNull Random random, int previousLayerSize, int layerSize) {
    if (previousLayerSize <= 0) {
      throw new IllegalArgumentException("previousLayerSize");
    }

    if (layerSize <= 0) {
      throw new IllegalArgumentException("layerSize");
    }
    this.previousLayerSize = previousLayerSize;
    this.layerSize = layerSize;
    this.biases = randn(random, layerSize);
    this.weights = randn(random, previousLayerSize * layerSize);
  }

  public Segment(int previousLayerSize, int layerSize) {
    this.previousLayerSize = previousLayerSize;
    this.layerSize = layerSize;
    this.biases = new float[layerSize];
    this.weights = new float[previousLayerSize * layerSize];
  }

  private Segment(@NonNull float[] biases, @NonNull float[] weights, int previousLayerSize) {
    this.previousLayerSize = previousLayerSize;
    this.layerSize = biases.length;
    this.biases = biases;
    this.weights = weights;

    // invariant check
    assert this.getLayerSize() * this.getPreviousLayerSize() == this.weights.length;
  }

  public int getLayerSize() {
    return this.layerSize;
  }

  public int getPreviousLayerSize() {
    return this.previousLayerSize;
  }

  public float[] feedforward(NeuralNetworkMetadata metadata, float[] previousLayerValues, Consumer<float[]> zConsumer) {
    final int previousLayerSize = previousLayerValues.length;
    final int layerSize = this.getLayerSize();

    if (this.getPreviousLayerSize() != previousLayerSize) {
      throw new IllegalStateException("Weight matrix size=" + this.getPreviousLayerSize() +
          " does not match previous layer size=" + previousLayerSize);
    }

    // initialize accumulated layer values with biases
    final float[] layerValues = Arrays.copyOf(this.biases, this.biases.length);
    assert layerValues.length == this.getLayerSize();

    // accumulate `w * a` values in layerValues
    int weightIndex = 0;
    for (int i = 0; i < previousLayerSize; ++i) {
      final float prevNodeValue = previousLayerValues[i];
      for (int j = 0; j < layerSize; ++j) {
        assert weightIndex == this.getIndex(i, j) : "weights matrix index mismatch";
        layerValues[j] += prevNodeValue * this.weights[weightIndex];
        ++weightIndex;
      }
    }

    // let callback accept z-values before transforming them using sigmoid function
    zConsumer.accept(layerValues);

    // calculate Sigmoid(Sum(W * A) + b) and put into layer values
    metadata.getActivation().accept(layerValues);

    return layerValues;
  }

  public void add(Segment other) {
    assert other.getLayerSize() == this.getLayerSize() && other.getPreviousLayerSize() == this.getPreviousLayerSize();

    // accumulate biases
    for (int i = 0; i < this.getLayerSize(); ++i) {
      this.biases[i] += other.biases[i];
    }

    // accumulate weights
    // and since other segment should be identical to current one, we can just flat iterate over the weight matrices
    for (int i = 0; i < this.weights.length; ++i) {
      this.weights[i] += other.weights[i];
    }
  }

  public void scaleSub(Segment other, double rate) {
    assert other.getLayerSize() == this.getLayerSize() && other.getPreviousLayerSize() == this.getPreviousLayerSize();

    for (int i = 0; i < this.getLayerSize(); ++i) {
      this.biases[i] -= rate * other.biases[i];
    }

    // since other segment should be identical to current one, we can just flat iterate over the weight matrices
    for (int i = 0; i < this.weights.length; ++i) {
      this.weights[i] -= rate * other.weights[i];
    }
  }

  public float[] mulTransposedWeights(float[] delta) {
    assert delta.length == getLayerSize();

    // TODO: fixme - this needs to be optimized further
    // we need to calculate delta using previous layer's weights:
    // Delta(L-1) = Transpose(W(L-1)) * Delta(L)
    final float[] nextDelta = new float[getPreviousLayerSize()];
    int weightIndex = 0;
    for (int u = 0; u < getPreviousLayerSize(); ++u) {
      // u iterates from 0 up to current layer size
      float d = 0.0f;
      for (int v = 0; v < getLayerSize(); ++v) {
        assert weightIndex == this.getIndex(u, v) : "weights index mismatch";
        d += delta[v] * this.weights[weightIndex];
        ++weightIndex;
      }
      nextDelta[u] = d;
    }

    // update delta array
    return nextDelta;
  }

  // infers backpropagated segment
  public Segment backpropagate(float[] delta, float[] prevLayerActivations) {
    final float[] weights = calcBackpropagatedWeights(delta, prevLayerActivations);
    return new Segment(delta, weights, this.getPreviousLayerSize());
  }


  private float[] calcBackpropagatedWeights(float[] delta, float[] prevLayerActivations) {
    // calculate matrix dot product: Delta*Transpose(A(prev))
    assert delta.length == this.getLayerSize();
    assert prevLayerActivations.length == this.getPreviousLayerSize();
    final float[] weights = new float[this.getPreviousLayerSize() * this.getLayerSize()];
    int k = 0; // on every iteration k maintains index value, i.e. k == getIndex(i, j)
    for (int i = 0; i < prevLayerActivations.length; ++i) {
      for (int j = 0; j < delta.length; ++j) {
        assert k == getIndex(i, j);
        weights[k] = prevLayerActivations[i] * delta[j];
        ++k;
      }
    }
    return weights;
  }
}
