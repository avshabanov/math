package com.alexshabanov.orderbook.parser;

import com.alexshabanov.orderbook.model.BookLogEntry;

import java.io.Closeable;
import java.io.IOException;

/**
 * @author Alexander Shabanov
 */
public interface BookLogParser extends Closeable {

  /**
   * Parses next record from the reader, returns null when stream EOF is reached.
   *
   * @return Parsed entry or null if EOF reached
   * @throws IOException On I/O error
   */
  BookLogEntry parse() throws IOException;
}
