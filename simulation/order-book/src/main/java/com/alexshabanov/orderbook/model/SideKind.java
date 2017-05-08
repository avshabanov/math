package com.alexshabanov.orderbook.model;

/**
 * Identifies order side (a bid or an ask).
 *
 * @author Alexander Shabanov
 */
public enum SideKind {

  /**
   * Identifies buy order type (a bid).
   */
  BUY("B"),

  /**
   * Identifies "sell" order type (an ask).
   */
  SELL("S");

  /**
   * Read-only array of values, this is to avoid reallocations in {@link #fromCode(String)} method.
   */
  private static final SideKind[] VALUES = values();

  private final String code;

  SideKind(String code) {
    this.code = code;
  }

  public static SideKind fromCode(String code) {
    for (final SideKind kind : VALUES) {
      if (kind.getCode().equals(code)) {
        return kind;
      }
    }

    throw new IllegalArgumentException("Unknown side code=" + code);
  }

  public String getCode() {
    return this.code;
  }
}
