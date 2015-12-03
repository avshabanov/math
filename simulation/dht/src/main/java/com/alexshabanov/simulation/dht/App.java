package com.alexshabanov.simulation.dht;

import com.alexshabanov.simulation.dht.storage.Dht;
import com.alexshabanov.simulation.dht.storage.DhtRequest;
import com.alexshabanov.simulation.dht.storage.DhtResponse;
import com.alexshabanov.simulation.dht.storage.support.SimpleDht;

import java.util.Arrays;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;

/**
 * Entry point.
 */
public final class App {

  public static void main(String[] args) throws Exception {
    System.out.println("DHT demo");
    demo(new SimpleDht());
  }

  private static void demo(Dht dht) throws ExecutionException, InterruptedException {
    Future<DhtResponse.Get> responseFuture = dht.run(DhtRequest.Get.byKey("key"));
    final byte[] bytes = responseFuture.get().getContentAsBytes();
    System.out.println("key associated with " + Arrays.toString(bytes));
  }
}
