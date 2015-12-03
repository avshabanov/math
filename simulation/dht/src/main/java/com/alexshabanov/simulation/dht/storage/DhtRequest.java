package com.alexshabanov.simulation.dht.storage;

/**
 */
public abstract class DhtRequest<TResponse extends DhtResponse> {

  public abstract Class<TResponse> getResponseClass();

  public abstract <R> R apply(Visitor<R> visitor);

  public interface Visitor<R> {
    default R visitUnknown(DhtRequest<?> request) {
      throw new UnsupportedOperationException("Unknown request " + request);
    }

    default R visitGet(DhtRequest.Get request) {
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
}
