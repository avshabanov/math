package com.alexshabanov.orderbook.model;

import java.math.BigDecimal;
import java.util.Objects;

/**
 * @author Alexander Shabanov
 */
public final class AddBookLogEntry extends BookLogEntry {
  private final BigDecimal price;
  private final SideKind sideType;

  public AddBookLogEntry(int timestamp, String orderId, int size, BigDecimal price, SideKind sideType) {
    super(timestamp, orderId, size);

    if (price == null || price.compareTo(BigDecimal.ZERO) < 0) {
      throw new IllegalArgumentException("Invalid price");
    }

    this.price = price;
    this.sideType = Objects.requireNonNull(sideType, "Side type is null");
  }

  public BigDecimal getPrice() {
    return price;
  }

  public SideKind getSideType() {
    return sideType;
  }

  @Override
  public AddBookLogEntry asAddEntry() {
    return this;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof AddBookLogEntry)) return false;
    if (!super.equals(o)) return false;

    AddBookLogEntry that = (AddBookLogEntry) o;

    return price.equals(that.price) && sideType == that.sideType;
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + price.hashCode();
    result = 31 * result + sideType.hashCode();
    return result;
  }

  @Override
  public String toString() {
    return String.format(
        "%d A %s %s %s %s",
        getTimestamp(),
        getOrderId(),
        getSideType() == SideKind.BUY ? "B" : "S",
        getPrice(),
        getSize());
  }
}
