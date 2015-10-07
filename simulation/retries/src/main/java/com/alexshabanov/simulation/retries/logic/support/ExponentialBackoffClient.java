package com.alexshabanov.simulation.retries.logic.support;

import com.alexshabanov.simulation.retries.logic.Reporter;

import java.util.concurrent.ThreadLocalRandom;

/**
 * @author Alexander Shabanov
 */
public final class ExponentialBackoffClient extends AbstractClient {
  public int initRetryTime = 50;

  public ExponentialBackoffClient(int taskId, Reporter reporter) {
    super(taskId, reporter);
  }

  @Override
  protected int getNextWaitTime(int attempt) {
    final int time = (1 + ThreadLocalRandom.current().nextInt(2 << attempt)) * initRetryTime;
    return time;
  }
}
