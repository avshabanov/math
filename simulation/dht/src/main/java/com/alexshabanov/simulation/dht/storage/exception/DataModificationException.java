package com.alexshabanov.simulation.dht.storage.exception;

public class DataModificationException extends DataAccessException {
  public DataModificationException() {
  }

  public DataModificationException(String message) {
    super(message);
  }

  public DataModificationException(String message, Throwable cause) {
    super(message, cause);
  }

  public DataModificationException(Throwable cause) {
    super(cause);
  }

  public DataModificationException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
    super(message, cause, enableSuppression, writableStackTrace);
  }
}
