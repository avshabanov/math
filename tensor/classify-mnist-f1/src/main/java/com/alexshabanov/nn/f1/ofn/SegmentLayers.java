package com.alexshabanov.nn.f1.ofn;

import lombok.NonNull;

import java.util.Arrays;
import java.util.function.Consumer;

/**
 * Encapsulates neuron activation metadata.
 */
public final class SegmentLayers {
  private final NeuronActivation[] activations;
  private final int[] sizes;

  public SegmentLayers(@NonNull NeuronActivation[] activations, @NonNull int[] sizes) {
    assert activations.length == sizes.length;
    this.activations = activations;
    this.sizes = sizes;
  }

  public int getCount() {
    return this.sizes.length;
  }

  public int getLayerSize(int layerIndex) {
    return this.sizes[layerIndex];
  }

  public Consumer<float[]> getActivation(int layerIndex) {
    // omit first layer (input)
    return this.activations[layerIndex + 1].getActivation();
  }

  public Consumer<float[]> getActivationPrime(int layerIndex) {
    // omit first layer (input)
    return this.activations[layerIndex + 1].getActivationPrime();
  }

  public static SegmentLayers of(@NonNull NeuronActivation act, int inputLayerSize) {
    return new SegmentLayers(new NeuronActivation[]{act}, new int[]{inputLayerSize});
  }

  public SegmentLayers add(@NonNull NeuronActivation act, int size) {
    final NeuronActivation[] newActivations = Arrays.copyOf(this.activations, this.activations.length + 1);
    final int[] newSizes = Arrays.copyOf(this.sizes, this.sizes.length + 1);

    newActivations[this.activations.length] = act;
    newSizes[this.sizes.length] = size;
    return new SegmentLayers(newActivations, newSizes);
  }

  public SegmentLayers add(int size) {
    return add(this.activations[this.activations.length - 1], size);
  }
}
