package com.alexshabanov.simulation.retries.logic;

/**
 * Client interface.
 *
 * @author Alexander Shabanov
 */
public interface Client {
  void interact(Server server);
}
