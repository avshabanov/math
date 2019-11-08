package com.alexshabanov.groups.utils;

import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.assertEquals;

public final class MoreStringsTest {

  @Test
  public void shouldReturnAppendable() throws IOException {
    final Appendable a = new StringBuilder();
    assertEquals(a, MoreStrings.append(a, ' ', 1));
    assertEquals(a, MoreStrings.padded(a, " ", 1));
  }
}
