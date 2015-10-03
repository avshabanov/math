package com.alexshabanov.simulation.retries.logic.support;

import com.alexshabanov.simulation.retries.logic.*;

import java.util.concurrent.ThreadLocalRandom;

/**
 * @author Alexander Shabanov
 */
public final class LinearBackoffClient extends AbstractClient {

  public int initRetryTime = 50;
  public double randMultiplier = 0.2;

  public LinearBackoffClient(int taskId, Reporter reporter) {
    super(taskId, reporter);
  }

  @Override
  protected int getNextWaitTime(int attempt) {
    int time = initRetryTime * (attempt + 1);
    time = time + ThreadLocalRandom.current().nextInt((int) (time * randMultiplier));
    return time;
  }
}
