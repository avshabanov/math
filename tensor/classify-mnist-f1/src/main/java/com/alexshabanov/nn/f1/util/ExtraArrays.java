package com.alexshabanov.nn.f1.util;

import java.util.Random;

/**
 * Array utilities.
 */
public final class ExtraArrays {
  private ExtraArrays() {}

  public static String floatsToString(float[] arr) {
    final StringBuilder sb = new StringBuilder(arr.length * 7 + 10).append('[');
    for (int i = 0; i < arr.length; ++i) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(String.format("%.2f", arr[i]));
    }
    return sb.append(']').toString();
  }
}
