package com.alexshabanov.simulation.dht.storage;

import java.util.concurrent.Future;

/**
 * DHT interface.
 */
public interface Dht {

  <TRequest extends DhtRequest<TResponse>, TResponse extends DhtResponse> Future<TResponse> run(TRequest request);
}
