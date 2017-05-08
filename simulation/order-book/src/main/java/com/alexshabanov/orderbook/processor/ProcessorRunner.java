package com.alexshabanov.orderbook.processor;

import com.alexshabanov.orderbook.model.BookLogEntry;
import com.alexshabanov.orderbook.parser.BookLogParser;

import java.io.PrintStream;

/**
 * Utility class for running book log processor against corresponding parser.
 *
 * @author Alexander Shabanov
 */
public final class ProcessorRunner {
  private ProcessorRunner() {}

  public static void runProcessor(BookLogProcessor processor, BookLogParser parser, PrintStream errorStream) {
    int lineNumber = 0;

    try {
      for (;;) {
        ++lineNumber;
        final BookLogEntry entry = parser.parse();
        if (entry == null) {
          break;
        }

        processor.process(entry);
      }
    } catch (Exception e) {
      errorStream.println("Error at line " + lineNumber + ":\n");
      errorStream.println(e.getMessage());
    }
  }
}
