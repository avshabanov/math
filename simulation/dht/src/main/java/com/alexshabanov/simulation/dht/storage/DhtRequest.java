package com.alexshabanov.simulation.dht.storage;

/**
 * Abstract request class.
 */
public abstract class DhtRequest<TResponse extends DhtResponse> {

  public abstract Class<TResponse> getResponseClass();

  public abstract <R> R apply(Visitor<R> visitor);

  public interface Visitor<R> {
    default R visitUnknown(DhtRequest<?> request) {
      throw new UnsupportedOperationException("Unknown request " + request);
    }

    default R visitGet(Get request) {
      return visitUnknown(request);
    }

    default R visitPut(Put request) {
      return visitUnknown(request);
    }
  }

  public static final class Get extends DhtRequest<DhtResponse.Get> {
    private final String key;

    private Get(String key) {
      this.key = key;
    }

    @Override
    public Class<DhtResponse.Get> getResponseClass() {
      return DhtResponse.Get.class;
    }

    @Override
    public <R> R apply(Visitor<R> visitor) {
      return visitor.visitGet(this);
    }

    public static Get byKey(String key) {
      return new Get(key);
    }

    public String getKey() {
      return key;
    }
  }

  public static final class Put extends DhtRequest<DhtResponse.Put> {
    private final String key;
    private final byte[] value;
    private final boolean includePrevContent;

    private Put(String key, byte[] value, boolean includePrevContent) {
      this.key = key;
      this.value = value;
      this.includePrevContent = includePrevContent;
    }

    public static Put byKeyValue(String key, byte[] value) {
      return new Put(key, value, true);
    }

    public String getKey() {
      return key;
    }

    public byte[] getValue() {
      return value;
    }

    public boolean isIncludePrevContent() {
      return includePrevContent;
    }

    @Override
    public Class<DhtResponse.Put> getResponseClass() {
      return DhtResponse.Put.class;
    }

    @Override
    public <R> R apply(Visitor<R> visitor) {
      return visitor.visitPut(this);
    }
  }
}
