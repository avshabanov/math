package com.alexshabanov.nn.f1.ofn;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Getter;
import lombok.NonNull;

import java.util.Random;

/**
 * Neural network metadata
 */
@Builder(toBuilder = true)
@Getter
@AllArgsConstructor
public final class NeuralNetworkMetadata {
  @NonNull
  private final Random random;
}
