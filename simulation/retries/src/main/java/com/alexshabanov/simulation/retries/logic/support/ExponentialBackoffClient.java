package com.alexshabanov.simulation.retries.logic.support;

import com.alexshabanov.simulation.retries.logic.Reporter;

import java.util.concurrent.ThreadLocalRandom;

/**
 * @author Alexander Shabanov
 */
public final class ExponentialBackoffClient extends AbstractClient {
  public int initRetryTime = 50;
  public double randMultiplier = 0.2;

  public ExponentialBackoffClient(int taskId, Reporter reporter) {
    super(taskId, reporter);
  }

  @Override
  protected int getNextWaitTime(int attempt) {
    int time = (int) (initRetryTime * Math.pow(2, attempt));
    time = time + ThreadLocalRandom.current().nextInt((int) (time * randMultiplier));
    return time;
  }
}
