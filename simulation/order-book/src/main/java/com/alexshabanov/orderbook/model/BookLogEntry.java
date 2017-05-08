package com.alexshabanov.orderbook.model;

/**
 * @author Alexander Shabanov
 */
public abstract class BookLogEntry {
  private final int timestamp;
  private final String orderId;
  private final long size;

  BookLogEntry(int timestamp, String orderId, long size) {
    if (size < 0) {
      throw new IllegalArgumentException("Negative size");
    }

    if (timestamp < 0) {
      throw new IllegalArgumentException("Negative timestamp");
    }

    if (orderId == null || orderId.length() == 0) {
      throw new IllegalArgumentException("orderId is null or empty");
    }

    this.timestamp = timestamp;
    this.orderId = orderId;
    this.size = size;
  }

  public int getTimestamp() {
    return timestamp;
  }

  public String getOrderId() {
    return orderId;
  }

  public long getSize() {
    return size;
  }

  /**
   * Attempts to cast this instance to {@link ReduceBookLogEntry}, returns null if it is not of this type.
   * @implNote introduce visitor pattern when number of descendant types becomes larger than just two entries.
   *
   * @return This instance casted to {@link ReduceBookLogEntry}, null if this cast is not possible
   */
  public ReduceBookLogEntry asReduceEntry() {
    return null;
  }

  /**
   * Attempts to cast this instance to {@link AddBookLogEntry}, returns null if it is not of this type.
   * @implNote introduce visitor pattern when number of descendant types becomes larger than just two entries.
   *
   * @return This instance casted to {@link AddBookLogEntry}, null if this cast is not possible
   */
  public AddBookLogEntry asAddEntry() {
    return null;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof BookLogEntry)) return false;

    BookLogEntry that = (BookLogEntry) o;

    return timestamp == that.timestamp && size == that.size && orderId.equals(that.orderId);
  }

  @Override
  public int hashCode() {
    int result = timestamp;
    result = 31 * result + orderId.hashCode();
    result = 31 * result + (int) (size ^ (size >>> 32));
    return result;
  }
}
