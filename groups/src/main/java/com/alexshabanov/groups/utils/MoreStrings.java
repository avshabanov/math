package com.alexshabanov.groups.utils;

import lombok.experimental.UtilityClass;

import java.io.IOException;

/**
 * String utility functions.
 */
@UtilityClass public class MoreStrings {

  public static Appendable append(Appendable appendable, char ch, int repeat) throws IOException {
    for (int i = 0; i < repeat; ++i) {
      appendable.append(ch);
    }
    return appendable;
  }

  public static Appendable padded(Appendable appendable, Object value, int maxWidth) throws IOException {
    final String valueString = String.valueOf(value);
    if (valueString.length() > maxWidth) {
      throw new IllegalArgumentException("value=" + value + " is exceeding maxWidth=" + maxWidth);
    }

    int leftPad = (maxWidth - valueString.length()) / 2;
    int remainingPad = maxWidth - leftPad - valueString.length();

    append(appendable, ' ', Math.max(leftPad, remainingPad));
    appendable.append(valueString);
    append(appendable, ' ', Math.min(leftPad, remainingPad));
    return appendable;
  }
}
