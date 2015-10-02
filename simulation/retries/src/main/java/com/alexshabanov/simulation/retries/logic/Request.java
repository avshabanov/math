package com.alexshabanov.simulation.retries.logic;

/**
 * Simulation request.
 *
 * @author Alexander Shabanov
 */
public final class Request {
  public final int taskId;

  public Request(int taskId) {
    this.taskId = taskId;
  }
}
