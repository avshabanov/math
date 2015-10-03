package com.alexshabanov.simulation.retries.logic.support;

import com.alexshabanov.simulation.retries.logic.*;

/**
 * @author Alexander Shabanov
 */
public final class ImmediateRetryClient extends AbstractClient {

  public ImmediateRetryClient(int taskId, Reporter reporter) {
    super(taskId, reporter);
  }

  @Override
  protected int getNextWaitTime(int attempt) {
    return 0;
  }
}
