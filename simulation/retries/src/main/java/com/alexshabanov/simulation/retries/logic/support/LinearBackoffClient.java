package com.alexshabanov.simulation.retries.logic.support;

import com.alexshabanov.simulation.retries.logic.*;

import java.util.concurrent.ThreadLocalRandom;

/**
 * @author Alexander Shabanov
 */
public final class LinearBackoffClient implements Client {
  private final Reporter reporter;
  private final int taskId;
  private Mode mode = Mode.NEW;

  public int waitTime = 0;
  public int lastRetryTime = 0;

  public int totalWaitTime = 0;
  public int initRetryTime = 10;
  public double multiplier = 1.5;
  public int maxRetryTime = 200;
  public double randMultiplier = 0.1;
  public boolean reportEnabled = false;

  public LinearBackoffClient(int taskId, Reporter reporter) {
    this.reporter = reporter;
    this.taskId = taskId;
  }

  @Override
  public void interact(Server server) {
    ++totalWaitTime;

    switch (mode) {
      case NEW:
        if (server.enqueue(new Request(taskId))) {
          mode = Mode.POLL;
        } else {
          waitTime = getNextWaitTime();
          if (waitTime < maxRetryTime) {
            lastRetryTime = waitTime;
            mode = Mode.BACKOFF;
          } else {
            reporter.reportRequest(totalWaitTime, false);
            totalWaitTime = 0;
            lastRetryTime = 0;
            mode = Mode.NEW;
          }
        }
        break;

      case POLL:
        final Response response = server.poll(taskId);
        if (response != null) {
          if (reportEnabled) {
            System.out.println("Processed request for task #" + taskId);
          }
          mode = Mode.NEW;
          reporter.reportRequest(totalWaitTime, true);
          totalWaitTime = 0;
        }
        break;

      case BACKOFF:
        if (--waitTime < 0) {
          mode = Mode.NEW;
        }
        break;

      default:
        throw new RuntimeException("Unknown mode=" + mode);
    }
  }

  //
  // Private
  //

  private int getNextWaitTime() {
    final int time = (lastRetryTime != 0 ? (int) (lastRetryTime * multiplier) : initRetryTime);
    return time + ThreadLocalRandom.current().nextInt((int) (time * randMultiplier));
  }

  private enum Mode {
    NEW,
    POLL,
    BACKOFF
  }
}
