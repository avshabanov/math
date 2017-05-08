package com.alexshabanov.orderbook.model;

/**
 * @author Alexander Shabanov
 */
public final class ReduceBookLogEntry extends BookLogEntry {
  public ReduceBookLogEntry(int timestamp, String orderId, int size) {
    super(timestamp, orderId, size);
  }

  @Override
  public ReduceBookLogEntry asReduceEntry() {
    return this;
  }

  @Override
  public boolean equals(Object o) {
    return o instanceof ReduceBookLogEntry && super.equals(o);
  }

  @Override
  public int hashCode() {
    return 31 + super.hashCode();
  }

  @Override
  public String toString() {
    return String.format("%d R %s %d", getTimestamp(), getOrderId(), getSize());
  }
}
