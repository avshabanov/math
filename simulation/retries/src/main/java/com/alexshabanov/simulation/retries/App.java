package com.alexshabanov.simulation.retries;

import com.alexshabanov.simulation.retries.logic.Client;
import com.alexshabanov.simulation.retries.logic.Reporter;
import com.alexshabanov.simulation.retries.logic.Server;
import com.alexshabanov.simulation.retries.logic.support.ImmediateRetryClient;
import com.alexshabanov.simulation.retries.logic.support.LinearBackoffClient;
import com.alexshabanov.simulation.retries.logic.support.ServerImpl;

import java.util.ArrayList;
import java.util.List;

/**
 * Entry point.
 */
public final class App implements Runnable, Reporter {

  private int succeededRequests = 0;
  private int succeededRequestsTime = 0;

  private int failedRequests = 0;
  private int failedRequestsTime = 0;

  public static void main(String[] args) {
    new App().run();
  }

  @Override
  public void reportRequest(int processTicks, boolean succeeded) {
    if (succeeded) {
      ++succeededRequests;
      succeededRequestsTime += processTicks;
    } else {
      ++failedRequests;
      failedRequestsTime += processTicks;
    }
  }

  @Override
  public void run() {
    ClientFactory clientFactory;

    System.out.println("== Immediate Retry ==");
    clientFactory = ImmediateRetryClient::new;
    runSimulation(5, 5, 100000, clientFactory); // 1:1
    runSimulation(10, 5, 100000, clientFactory); // 2x overload
    runSimulation(20, 5, 100000, clientFactory); // 4x overload

    System.out.println("== Linear Backoff Retry ==");
    clientFactory = LinearBackoffClient::new;
    runSimulation(5, 5, 100000, clientFactory); // 1:1
    runSimulation(10, 5, 100000, clientFactory); // 2x overload
    runSimulation(20, 5, 100000, clientFactory); // 4x overload

    System.out.println("===");
  }

  private interface ClientFactory {
    Client create(int taskId, Reporter reporter);
  }

  private void runSimulation(int clientCount, int maxServerTaskCount, int maxTicks, ClientFactory factory) {
    succeededRequests = 0;
    succeededRequestsTime = 0;
    failedRequests = 0;
    failedRequestsTime = 0;

    // init clients
    final List<Client> clients = new ArrayList<>();
    for (int i = 0; i < clientCount; ++i) {
      clients.add(factory.create(i, this));
    }

    // run loops
    final Server server = new ServerImpl(maxServerTaskCount, 50);
    for (int i = 0; i < maxTicks; ++i) {
      for (final Client client : clients) {
        client.interact(server);
      }
      server.tick();
    }

    // calc statistics
    System.out.println("clientCount=" + clientCount + ", maxServerTaskCount=" + maxServerTaskCount +
        ", maxTicks=" + maxTicks);
    System.out.println("\tSucceeded requests=" + succeededRequests +
        " p100 time=" + (succeededRequests > 0 ? (succeededRequestsTime * 1.0 / succeededRequests) : 0) +
        " Failed requests=" + failedRequests +
        " p100 time=" + (failedRequests > 0 ? (failedRequestsTime * 1.0 / failedRequests) : 0) +
        "");
  }
}
