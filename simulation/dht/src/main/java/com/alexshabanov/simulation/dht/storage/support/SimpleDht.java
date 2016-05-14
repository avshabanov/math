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
  private final Map<String, byte[]> map;

  public SimpleDht() {
    map = new HashMap<>(100);
  }

  @Override
  public <TRequest extends DhtRequest<TResponse>, TResponse extends DhtResponse> Future<TResponse> run(TRequest request) {
    return request.apply(new DhtRequest.Visitor<Future<TResponse>>() {
      @Override
      public Future<TResponse> visitGet(DhtRequest.Get request) {
        final Future<DhtResponse.Get> response = new ImmediateFuture<>(DhtResponse.Get.fromBytes(map.get(request.getKey())));
        //noinspection unchecked
        return (Future<TResponse>) response;
      }

      @Override
      public Future<TResponse> visitPut(DhtRequest.Put request) {
        final byte[] prevContent = map.put(request.getKey(), request.getValue());
        final byte[] includedContent = request.isIncludePrevContent() ? prevContent : null;

        final Future<DhtResponse.Put> response = new ImmediateFuture<>(DhtResponse.Put.fromBytes(includedContent));
        //noinspection unchecked
        return (Future<TResponse>) response;
      }
    });
  }
}
