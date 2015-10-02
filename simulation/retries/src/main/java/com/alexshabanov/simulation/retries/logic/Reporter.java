package com.alexshabanov.simulation.retries.logic;

/**
 * @author Alexander Shabanov
 */
public interface Reporter {
  void reportRequest(int processTicks, boolean succeeded);
}
