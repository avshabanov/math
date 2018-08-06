package com.alexshabanov.nn.f1.ofn;

import lombok.AllArgsConstructor;
import lombok.NonNull;

import java.util.Arrays;

/**
 * Represents series of segments.
 */
@AllArgsConstructor
public class Segments {
  private final Segment[] segments;

  public int size() {
    return this.segments.length;
  }

  public Segment get(int index) {
    return this.segments[index];
  }

  // Creates new segments, where all biases and weights are initialized to zeroes
  public static Segments createPrototype(@NonNull Segments template) {
    return new Segments(Arrays.stream(template.segments)
        .map(x -> new Segment(x.getPreviousLayerSize(), x.getLayerSize()))
        .toArray(Segment[]::new));
  }
}
