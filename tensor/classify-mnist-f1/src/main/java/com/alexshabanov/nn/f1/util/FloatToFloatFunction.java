package com.alexshabanov.nn.f1.util;

import java.util.function.Function;

/**
 * Unboxed alternative to float function.
 */
@FunctionalInterface
public interface FloatToFloatFunction extends Function<Float, Float> {

  float applyUnboxed(float value);

  @Override
  default Float apply(Float value) {
    return applyUnboxed(value);
  }
}
