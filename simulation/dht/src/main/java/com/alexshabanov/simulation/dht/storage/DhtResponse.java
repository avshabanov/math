package com.alexshabanov.simulation.dht.storage;

/**
 * Interface to the response.
 */
public abstract class DhtResponse {

  public static final class Get extends DhtResponse {

    private final byte[] content;

    public Get(byte[] content) {
      this.content = content;
    }

    public static Get fromBytes(byte[] content) {
      return new Get(content);
    }

    public byte[] getContentAsBytes() {
      return content;
    }
  }

  public static final class Put extends DhtResponse {

    private final byte[] prevContent;

    public Put(byte[] prevContent) {
      this.prevContent = prevContent;
    }

    public static Put fromBytes(byte[] content) {
      return new Put(content);
    }

    public byte[] getPreviousContentAsBytes() {
      return prevContent;
    }
  }
}
