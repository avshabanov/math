package com.alexshabanov.math.nn;

import org.junit.Test;

import java.util.BitSet;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public final class DiscreteGateChainTest {

  @Test
  public void shouldInitializeAsNandGate() {
    final DiscreteGateChain chain = new DiscreteGateChain(2, 1);
    chain.setWeightsAndBiases();

    assertTrue(toBit(chain.evaluate(bits(false, false))));
    assertFalse(toBit(chain.evaluate(bits(false, true))));
    assertFalse(toBit(chain.evaluate(bits(true, false))));
    assertFalse(toBit(chain.evaluate(bits(true, true))));
  }

  static boolean toBit(BitSet r) {
    assertTrue(r.length() <= 1);
    return r.get(0);
  }

  static BitSet bits(boolean... values) {
    final BitSet r = new BitSet(values.length);
    for (int i = 0; i < values.length; ++i) {
      r.set(i, values[i]);
    }
    return r;
  }
}
