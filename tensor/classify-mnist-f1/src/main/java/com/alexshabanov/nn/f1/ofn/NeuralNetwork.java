package com.alexshabanov.nn.f1.ofn;

import com.alexshabanov.nn.f1.cost.CostFunction;
import lombok.NonNull;

import java.util.Random;

/**
 * Represents context for a neural network.
 */
public interface NeuralNetwork {

  Random getRandom();

  Segments getSegments();

  SegmentLayers getSegmentLayers();

  CostFunction getCostFunction();

  float[] evaluate(@NonNull float[] input);
}
