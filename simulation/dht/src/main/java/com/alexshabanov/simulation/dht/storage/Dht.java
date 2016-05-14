package com.alexshabanov.simulation.dht.storage;

import com.alexshabanov.simulation.dht.storage.exception.DataModificationException;
import com.alexshabanov.simulation.dht.storage.exception.DataRetrievalException;

import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;

/**
 * DHT interface.
 */
public interface Dht {

  <TRequest extends DhtRequest<TResponse>, TResponse extends DhtResponse> Future<TResponse> run(TRequest request);

  default byte[] get(String key) {
    final Future<DhtResponse.Get> response = run(DhtRequest.Get.byKey(key));
    try {
      final DhtResponse.Get result = response.get();
      return result.getContentAsBytes();
    } catch (InterruptedException | ExecutionException e) {
      throw new DataRetrievalException(e);
    }
  }

  default byte[] put(String key, byte[] value) {
    final Future<DhtResponse.Put> response = run(DhtRequest.Put.byKeyValue(key, value));
    try {
      final DhtResponse.Put result = response.get();
      return result.getPreviousContentAsBytes();
    } catch (InterruptedException | ExecutionException e) {
      throw new DataModificationException(e);
    }
  }
}
