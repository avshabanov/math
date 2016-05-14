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

  private static void demo(Dht dht) {
    dht.put("key", new byte[] {1, 2, 3});
    byte[] bytes = dht.get("key");
    System.out.println("[1] key associated with " + Arrays.toString(bytes));

    dht.put("key", new byte[] {4, 5});
    bytes = dht.get("key");
    System.out.println("[2] key associated with " + Arrays.toString(bytes));
  }
}
