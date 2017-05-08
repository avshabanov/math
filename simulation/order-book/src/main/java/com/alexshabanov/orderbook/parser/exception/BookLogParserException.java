package com.alexshabanov.orderbook.parser.exception;

import java.io.IOException;

/**
 * Base class for book log parser exception.
 *
 * @author Alexander Shabanov
 */
public class BookLogParserException extends IOException {

  public BookLogParserException() {
  }

  public BookLogParserException(String message) {
    super(message);
  }

  public BookLogParserException(String message, Throwable cause) {
    super(message, cause);
  }

  public BookLogParserException(Throwable cause) {
    super(cause);
  }
}
