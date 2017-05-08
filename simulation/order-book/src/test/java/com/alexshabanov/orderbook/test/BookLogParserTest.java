package com.alexshabanov.orderbook.test;

import com.alexshabanov.orderbook.model.AddBookLogEntry;
import com.alexshabanov.orderbook.model.BookLogEntry;
import com.alexshabanov.orderbook.model.ReduceBookLogEntry;
import com.alexshabanov.orderbook.model.SideKind;
import com.alexshabanov.orderbook.parser.BookLogParser;
import com.alexshabanov.orderbook.parser.support.DefaultBookLogParser;
import org.junit.Test;

import java.io.IOException;
import java.io.StringReader;
import java.math.BigDecimal;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

/**
 * @author Alexander Shabanov
 */
public final class BookLogParserTest {

  @Test
  public void shouldParseNoEntries() throws IOException {
    try (final BookLogParser parser = new DefaultBookLogParser(new StringReader(""))) {
      assertNull(parser.parse());
    }
  }

  @Test
  public void shouldParseSingleAddBookEntry() throws IOException {
    try (final BookLogParser parser = new DefaultBookLogParser(new StringReader("12345678 A abc S 43.21 321"))) {
      final BookLogEntry entry = parser.parse();
      assertEquals(
          new AddBookLogEntry(12345678, "abc", 321, new BigDecimal("43.21"), SideKind.SELL),
          entry.asAddEntry());

      // last read should fail
      assertNull(parser.parse());
    }
  }

  @Test
  public void shouldParseSingleReduceBookEntry() throws IOException {
    try (final BookLogParser parser = new DefaultBookLogParser(new StringReader("12345678 R abc 12\n"))) {
      final BookLogEntry entry = parser.parse();
      assertEquals(
          new ReduceBookLogEntry(12345678, "abc", 12),
          entry.asReduceEntry());

      // last read should fail
      assertNull(parser.parse());
    }
  }

  @Test
  public void shouldParseMultipleEntries() throws IOException {
    try (final BookLogParser parser = new DefaultBookLogParser(new StringReader(
        "12345678 A abc B 43.21 321\n" +
            "12345678 R abc 12\n"))) {
      BookLogEntry entry;

      entry = parser.parse();
      assertEquals(
          new AddBookLogEntry(12345678, "abc", 321, new BigDecimal("43.21"), SideKind.BUY),
          entry.asAddEntry());

      entry = parser.parse();
      assertEquals(
          new ReduceBookLogEntry(12345678, "abc", 12),
          entry.asReduceEntry());

      // next read should fail
      assertNull(parser.parse());
    }
  }

  @Test(expected = IOException.class)
  public void shouldRejectTimestampOnlyEntry() throws IOException {
    try (final BookLogParser parser = new DefaultBookLogParser(new StringReader("12345678\n"))) {
      parser.parse();
    }
  }

  @Test(expected = IOException.class)
  public void shouldRejectTimestampTypeAndOrderOnlyEntry() throws IOException {
    try (final BookLogParser parser = new DefaultBookLogParser(new StringReader("12345678 R abc\n"))) {
      parser.parse();
    }
  }

  @Test(expected = IOException.class)
  public void shouldRejectReduceEntryWithExcessiveTokens() throws IOException {
    try (final BookLogParser parser = new DefaultBookLogParser(new StringReader("12345678 R abc 1 1\n"))) {
      parser.parse();
    }
  }

  @Test(expected = IOException.class)
  public void shouldRejectAddEntryWithExcessiveTokens() throws IOException {
    try (final BookLogParser parser = new DefaultBookLogParser(new StringReader("12345678 A abc S 43.21 321 1\n"))) {
      parser.parse();
    }
  }
}
