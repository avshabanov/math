package com.alexshabanov.simulation.dht.storage.exception;

public class DataRetrievalException extends DataAccessException {
  public DataRetrievalException() {
  }

  public DataRetrievalException(String message) {
    super(message);
  }

  public DataRetrievalException(String message, Throwable cause) {
    super(message, cause);
  }

  public DataRetrievalException(Throwable cause) {
    super(cause);
  }

  public DataRetrievalException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
    super(message, cause, enableSuppression, writableStackTrace);
  }
}
