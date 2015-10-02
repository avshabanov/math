package com.alexshabanov.simulation.retries.logic;

/**
 * Simulated server.
 *
 * @author Alexander Shabanov
 */
public interface Server {
  boolean enqueue(Request request);
  void tick();
  Response poll(int taskId);
}
