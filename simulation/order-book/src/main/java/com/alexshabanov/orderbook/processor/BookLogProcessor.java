package com.alexshabanov.orderbook.processor;

import com.alexshabanov.orderbook.model.BookLogEntry;

import java.io.Closeable;

/**
 * @author Alexander Shabanov
 */
public interface BookLogProcessor extends Closeable {

  void process(BookLogEntry entry);
}
