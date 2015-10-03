package com.alexshabanov.simulation.retries.logic.support;

import com.alexshabanov.simulation.retries.logic.Client;
import com.alexshabanov.simulation.retries.logic.Reporter;
import com.alexshabanov.simulation.retries.logic.Request;
import com.alexshabanov.simulation.retries.logic.Response;
import com.alexshabanov.simulation.retries.logic.Server;

/**
 * Abstract implementation of a client.
 */
public class AbstractClient implements Client {
  private final Reporter reporter;
  private final int taskId;
  private final int maxRetries;

  private Mode mode = Mode.NEW;
  private int retryIndex;
  private int waitTime = 0;

  private int totalWaitTime = 0;

  public AbstractClient(int taskId, Reporter reporter) {
    this.reporter = reporter;
    this.taskId = taskId;
    this.maxRetries = 5;
  }

  @Override
  public void interact(Server server) {
    switch (mode) {
      case NEW:
        if (server.enqueue(new Request(taskId))) {
          mode = Mode.POLL;
        } else {
          if (retryIndex < maxRetries) {
            waitTime = getNextWaitTime(retryIndex);
            ++retryIndex;
            mode = Mode.BACKOFF;
          } else {
            reporter.reportRequest(totalWaitTime, false);
            totalWaitTime = 0;
            retryIndex = 0;
            mode = Mode.NEW;
          }
        }
        break;

      case POLL:
        ++totalWaitTime;
        final Response response = server.poll(taskId);
        if (response != null) {
          if (isReportEnabled()) {
            System.out.println("Processed request for task #" + taskId);
          }
          mode = Mode.NEW;
          reporter.reportRequest(totalWaitTime, true);
          totalWaitTime = 0;
        }
        break;

      case BACKOFF:
        ++totalWaitTime;
        if (--waitTime < 0) {
          mode = Mode.NEW;
        }
        break;

      default:
        throw new RuntimeException("Unknown mode=" + mode);
    }
  }

  protected int getNextWaitTime(int attempt) {
    return -1; // no retries
  }

  protected boolean isReportEnabled() {
    return false;
  }

  //
  // Private
  //

  private enum Mode {
    NEW,
    POLL,
    BACKOFF
  }
}
