package com.alexshabanov.simulation.dht.storage.support;

import com.alexshabanov.simulation.dht.storage.Dht;
import com.alexshabanov.simulation.dht.storage.DhtRequest;
import com.alexshabanov.simulation.dht.storage.DhtResponse;
import com.alexshabanov.simulation.dht.util.ImmediateFuture;
import com.sun.xml.internal.ws.util.CompletedFuture;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.Future;

/**
 * TODO: implement
 */
public class SimpleDht implements Dht {
  private final Map<String, byte[]> map = new HashMap<>();

  public SimpleDht() {
    this.map.put("key", new byte[] { 1, 2, 3 });
  }

  @Override
  public <TRequest extends DhtRequest<TResponse>, TResponse extends DhtResponse> Future<TResponse> run(TRequest request) {
    return request.apply(new DhtRequest.Visitor<Future<TResponse>>() {
      @Override
      public Future<TResponse> visitGet(DhtRequest.Get request) {
        final Future<?> response = new ImmediateFuture<>(DhtResponse.Get.fromBytes(map.get(request.getKey())));
        //noinspection unchecked
        return (Future<TResponse>) response;
      }
    });
  }
}
