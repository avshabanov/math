package com.alexshabanov.simulation.retries.logic.support;

import com.alexshabanov.simulation.retries.logic.Client;
import com.alexshabanov.simulation.retries.logic.Reporter;
import com.alexshabanov.simulation.retries.logic.Server;

/**
 * @author Alexander Shabanov
 */
public final class LinearBackoffClient implements Client {
  private final Reporter reporter;
  private final int taskId;
  public int waitTime = 0;
  public int lastRetryTime = 0;
  public int startRetryTime = 1;
  public double multiplier = 2.0;
  public int maxRetryTime = 5;

  public LinearBackoffClient(int taskId, Reporter reporter) {
    this.reporter = reporter;
    this.taskId = taskId;
  }

  @Override
  public void interact(Server server) {

  }
}
