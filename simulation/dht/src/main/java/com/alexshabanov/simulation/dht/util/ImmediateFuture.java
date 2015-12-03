package com.alexshabanov.simulation.dht.util;

import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

/**
 * @author Alexander Shabanov
 */
public class ImmediateFuture<T> implements Future<T> {
  private final T v;

  public ImmediateFuture(T v) {
    this.v = v;
  }

  public boolean cancel(boolean mayInterruptIfRunning) {
    return false;
  }

  public boolean isCancelled() {
    return false;
  }

  public boolean isDone() {
    return true;
  }

  public T get() throws ExecutionException {
    return this.v;
  }

  public T get(long timeout, TimeUnit unit) throws ExecutionException {
    return this.get();
  }
}
