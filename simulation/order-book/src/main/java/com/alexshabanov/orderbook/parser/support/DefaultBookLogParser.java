package com.alexshabanov.orderbook.parser.support;

import com.alexshabanov.orderbook.model.AddBookLogEntry;
import com.alexshabanov.orderbook.model.BookLogEntry;
import com.alexshabanov.orderbook.model.ReduceBookLogEntry;
import com.alexshabanov.orderbook.model.SideKind;
import com.alexshabanov.orderbook.parser.BookLogParser;
import com.alexshabanov.orderbook.parser.exception.BookLogParserException;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.math.BigDecimal;

/**
 * Default implementation of {@link BookLogParser}.
 *
 * @author Alexander Shabanov
 */
public final class DefaultBookLogParser implements BookLogParser {
  private final BufferedReader reader;

  public DefaultBookLogParser(Reader reader) {
    this.reader = new BufferedReader(reader);
  }

  @Override
  public BookLogEntry parse() throws IOException {
    // TODO: line is different on unix and windows, make this code line ending-agnostic depending on the runtime
    String line = this.reader.readLine();
    if (line == null) {
      // end of stream reached
      return null;
    }

    // NOTE: parser optimization is possible here: instead of reading as a string and splitting into tokens which
    // requires extra allocations of memory, we can use internal buffer stored as class instance variable and parse
    // that buffer in place as opposed to splitting string in tokens to avoid extra memory allocations.
    // This would increase speed and reduce GC work.
    final String[] tokens = line.split(" ");

    // at least four tokens required if it is reduce order entry and six if it is add order entry
    if (tokens.length < 4) {
      throw new IOException("Too few tokens");
    }

    // parse entry "header" or common tokens that every book message should have
    final int timestamp = parseIntValue(tokens[0], "timestamp");
    final char entryType = (tokens[1].length() == 1 ? tokens[1].charAt(0) : '?');
    final String orderId = tokens[2];

    final int size;


    // parse the remainder of log entry depending on the entry type
    switch (entryType) {
      case 'A':
        if (tokens.length != 6) {
          throw new IOException("Malformed add order entry");
        }
        final SideKind sideKind = SideKind.fromCode(tokens[3]);
        final BigDecimal price = parsePrice(tokens[4]);
        size = parseIntValue(tokens[5], "size");
        return new AddBookLogEntry(timestamp, orderId, size, price, sideKind);

      case 'R':
        if (tokens.length != 4) {
          throw new IOException("Malformed remove order entry");
        }
        size = parseIntValue(tokens[3], "size");
        return new ReduceBookLogEntry(timestamp, orderId, size);

      default:
        throw new IOException("Invalid entry type=" + tokens[1]);
    }
  }

  @Override
  public void close() throws IOException {
    this.reader.close();
  }

  //
  // Private
  //

  private int parseIntValue(String token, String parameterName) throws BookLogParserException {
    try {
      return Integer.parseInt(token);
    } catch (NumberFormatException e) {
      throw new BookLogParserException("Invalid " + parameterName + "=" + token, e);
    }
  }

  private BigDecimal parsePrice(String token) throws BookLogParserException {
    try {
      // TODO: we need to make this locale neutral if it makes sense in the runtime environment
      return new BigDecimal(token);
    } catch (NumberFormatException e) {
      throw new BookLogParserException("Invalid price=" + token);
    }
  }
}
