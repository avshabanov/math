package com.alexshabanov.simulation.retries.logic;

/**
 * Simulated server response
 *
 * @author Alexander Shabanov
 */
public final class Response {
  public final int taskId;
  public final String content;

  public Response(int taskId, String content) {
    this.taskId = taskId;
    this.content = content;
  }
}
