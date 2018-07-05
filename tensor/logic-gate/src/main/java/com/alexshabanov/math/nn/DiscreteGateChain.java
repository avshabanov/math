package com.alexshabanov.math.nn;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

public final class DiscreteGateChain {
  private final List<Segment> segments;

  public DiscreteGateChain(int... sizes) {
    if (sizes.length == 0) {
      throw new IllegalArgumentException("sizes");
    }

    this.segments = new ArrayList<>(sizes.length - 1);
    for (int i = 1; i < sizes.length; ++i) {
      this.segments.add(new Segment(sizes[i - 1], sizes[1]));
    }
  }

  public BitSet evaluate(BitSet input) {
    BitSet it = input;
    for (final Segment segment : this.segments) {
      assert it.length() <= segment.previousLayerSize;
      final BitSet activations = new BitSet(segment.getLayerSize());

      for (int j = 0; j < segment.getLayerSize(); ++j) {
        boolean base = false;

        for (int k = 0; k < segment.previousLayerSize; ++k) {
          base = base | (segment.getWeight(k, j) & it.get(k));
        }

        base = base ^ segment.biases.get(j);
        activations.set(j, base);
      }

      it = activations;
    }
    return it;
  }

  public void setWeightsAndBiases() {
    for (final Segment segment : this.segments) {
      segment.biases.set(0, segment.getLayerSize());
      segment.weights.set(0, segment.getLayerSize() * segment.getPreviousLayerSize());
    }
  }

  //
  // Private
  //

  private static final class Segment {
    final BitSet biases;
    final BitSet weights;
    final int layerSize;
    final int previousLayerSize;

    Segment(int previousLayerSize, int layerSize) {
      if (previousLayerSize <= 0) {
        throw new IllegalArgumentException("previousLayerSize");
      }

      if (layerSize <= 0) {
        throw new IllegalArgumentException("layerSize");
      }

      this.layerSize = layerSize;
      this.previousLayerSize = previousLayerSize;
      this.biases = new BitSet(layerSize);
      this.weights = new BitSet(layerSize * previousLayerSize);
    }

    public int getPreviousLayerSize() {
      return this.previousLayerSize;
    }

    int getLayerSize() {
      return this.layerSize;
    }

    boolean getWeight(int previousLayerNodeIndex, int layerNodeIndex) {
      return this.weights.get(getWeightBitSetIndex(previousLayerNodeIndex, layerNodeIndex));
    }

    void setWeight(int previousLayerNodeIndex, int layerNodeIndex, boolean value) {
      if (value) {
        this.weights.set(getWeightBitSetIndex(previousLayerNodeIndex, layerNodeIndex));
      } else {
        this.weights.clear(getWeightBitSetIndex(previousLayerNodeIndex, layerNodeIndex));
      }
    }

    private int getWeightBitSetIndex(int previousLayerNodeIndex, int layerNodeIndex) {
      if (previousLayerNodeIndex < 0 || previousLayerNodeIndex >= this.getPreviousLayerSize()) {
        throw new IllegalArgumentException("previousLayerNodeIndex");
      }
      if (layerNodeIndex < 0 || layerNodeIndex >= this.getLayerSize()) {
        throw new IllegalArgumentException("layerNodeIndex");
      }
      return previousLayerNodeIndex * getLayerSize() + layerNodeIndex;
    }
  }
}
