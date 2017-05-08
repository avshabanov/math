package com.alexshabanov.orderbook;

import com.alexshabanov.orderbook.parser.BookLogParser;
import com.alexshabanov.orderbook.parser.support.DefaultBookLogParser;
import com.alexshabanov.orderbook.processor.BookLogProcessor;
import com.alexshabanov.orderbook.processor.ProcessorRunner;
import com.alexshabanov.orderbook.processor.support.TargetSizeAnalyzer;

import java.io.IOException;
import java.io.InputStreamReader;

/**
 * Entry point.
 *
 * @author Alexander Shabanov
 */
public final class Main {

  public static void main(String[] args) throws IOException {
    if (args.length != 1) {
      printUsageAndExit("One command line argument expected");
      return;
    }

    long targetSize = -1;
    try {
      targetSize = Long.parseLong(args[0]);
    } catch (NumberFormatException ignored) {
      printUsageAndExit("Can't parse target-size command line parameter");
    }

    try (final BookLogParser parser = new DefaultBookLogParser(new InputStreamReader(System.in))) {
      try (final BookLogProcessor processor = new TargetSizeAnalyzer(System.out, targetSize)) {
        ProcessorRunner.runProcessor(processor, parser, System.err);
      }
    }
  }

  //
  // Private
  //

  private static void printUsageAndExit(String error) {
    System.err.println("Error: " + error);
    System.err.println("Usage: java -jar order-book.jar <target-size>");
    System.exit(-1);
  }
}
