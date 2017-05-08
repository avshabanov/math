package com.alexshabanov.orderbook.test;

import com.alexshabanov.orderbook.parser.BookLogParser;
import com.alexshabanov.orderbook.parser.support.DefaultBookLogParser;
import com.alexshabanov.orderbook.processor.BookLogProcessor;
import com.alexshabanov.orderbook.processor.ProcessorRunner;
import com.alexshabanov.orderbook.processor.support.TargetSizeAnalyzer;
import org.junit.Before;
import org.junit.Test;

import java.io.*;
import java.nio.charset.StandardCharsets;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * @author Alexander Shabanov
 */
public final class BookLogProcessorTest {
  private static final String CONTENTS = "28800538 A b S 44.26 100\n" +
      "28800562 A c B 44.10 100\n" +
      "28800744 R b 100\n" +
      "28800758 A d B 44.18 157\n" +
      "28800773 A e S 44.38 100\n" +
      "28800796 R d 157\n" +
      "28800812 A f B 44.18 157\n" +
      "28800974 A g S 44.27 100\n" +
      "28800975 R e 100\n" +
      "28812071 R f 100\n" +
      "28813129 A h B 43.68 50\n" +
      "28813300 R f 57\n" +
      "28813830 A i S 44.18 100\n" +
      "28814087 A j S 44.18 1000\n" +
      "28814834 R c 100\n" +
      "28814864 A k B 44.09 100\n" +
      "28815774 R k 100\n" +
      "28815804 A l B 44.07 175\n" +
      "28815937 R j 1000\n" +
      "28816245 A m S 44.22 100";

  private ByteArrayOutputStream out;
  private PrintStream outStream;

  private ByteArrayOutputStream err;
  private PrintStream errStream;

  @Before
  public void init() throws UnsupportedEncodingException {
    out = new ByteArrayOutputStream(1000);
    outStream = new PrintStream(out, true, StandardCharsets.UTF_8.name());

    err = new ByteArrayOutputStream(1000);
    errStream = new PrintStream(err, true, StandardCharsets.UTF_8.name());
  }

  @Test
  public void shouldAnalyzeStream() throws IOException {
    try (final BookLogParser parser = new DefaultBookLogParser(new StringReader(CONTENTS))) {
      try (final BookLogProcessor processor = new TargetSizeAnalyzer(outStream, 200)) {
        ProcessorRunner.runProcessor(processor, parser, errStream);
      }
    }

    final String outContents = new String(out.toByteArray(), StandardCharsets.UTF_8);
    final String errContents = new String(err.toByteArray(), StandardCharsets.UTF_8);

    assertTrue(outContents.length() > 0);
    assertEquals("28800758 S 8832.56\n" +
        "28800796 S NA\n" +
        "28800812 S 8832.56\n" +
        "28800974 B 8865.00\n" +
        "28800975 B NA\n" +
        "28812071 S NA\n" +
        "28813129 S 8806.50\n" +
        "28813300 S NA\n" +
        "28813830 B 8845.00\n" +
        "28814087 B 8836.00\n" +
        "28815804 S 8804.25\n" +
        "28815937 B 8845.00\n" +
        "28816245 B 8840.00\n", outContents);

    assertEquals("", errContents);
  }
}
