package com.alexshabanov.simulation.retries.logic.support;

import com.alexshabanov.simulation.retries.logic.Reporter;

/**
 * @author Alexander Shabanov
 */
public final class LinearBackoffClient extends AbstractClient {

  public int initRetryTime = 50;

  public LinearBackoffClient(int taskId, Reporter reporter) {
    super(taskId, reporter);
  }

  @Override
  protected int getNextWaitTime(int attempt) {
    final int time = initRetryTime * (attempt + 1);
    return time;
  }
}
