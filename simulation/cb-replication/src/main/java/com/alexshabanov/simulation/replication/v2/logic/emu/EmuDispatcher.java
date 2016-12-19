package com.alexshabanov.simulation.replication.v2.logic.emu;

import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * @author Alexander Shabanov
 */
public final class EmuDispatcher {
  private final ConcurrentHashMap<String, EmuEntityCounter> counters = new ConcurrentHashMap<>();

  //
  // Private
  //

  private static final class EmuEntityCounter {
    final AtomicLong counter = new AtomicLong(1L);
  }
}
