package com.alexshabanov.simulation.retries.logic.support;

import com.alexshabanov.simulation.retries.logic.*;

/**
 * @author Alexander Shabanov
 */
public final class ImmediateRetryClient implements Client {
  private final Reporter reporter;
  private final int taskId;

  private final int maxRetries;

  private Mode mode = Mode.NEW;

  private int retryCount = 0;
  private int totalWaitTime = 0;

  public ImmediateRetryClient(int taskId, Reporter reporter) {
    this.taskId = taskId;
    this.reporter = reporter;
    this.maxRetries = 3;
  }

  @Override
  public void interact(Server server) {
    ++totalWaitTime;

    switch (mode) {
      case NEW:
        if (server.enqueue(new Request(taskId))) {
          mode = Mode.POLL;
        } else {
          ++retryCount;
          if (retryCount > maxRetries) {
            reporter.reportRequest(totalWaitTime, false);
          }
          mode = Mode.NEW; // resubmit this request immediately
          totalWaitTime = 0;
        }
        break;

      case POLL:
        final Response response = server.poll(taskId);
        if (response != null) {
          reporter.reportRequest(totalWaitTime, true);
          totalWaitTime = 0;
          mode = Mode.NEW;
        }
        break;

      default:
        throw new RuntimeException("Unexpected mode=" + mode);
    }
  }

  //
  // Private
  //

  private enum Mode {
    NEW,
    POLL
  }
}
