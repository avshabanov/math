package com.alexshabanov.simulation.loadBalancing;

import com.alexshabanov.simulation.loadBalancing.logic.LoadBalancer;
import com.alexshabanov.simulation.loadBalancing.logic.LoadBalancerStrategy;
import com.alexshabanov.simulation.loadBalancing.logic.strategy.ExactDistributionLoadBalancerStrategy;
import com.alexshabanov.simulation.loadBalancing.logic.strategy.RandomLoadBalancerStrategy;
import com.alexshabanov.simulation.loadBalancing.logic.strategy.RandomPickCompareLoadBalancerStrategy;

/**
 * Entry point.
 */
public final class App {

  public static void main(String[] args) {
    simulate(new ExactDistributionLoadBalancerStrategy());
    simulate(new RandomLoadBalancerStrategy());
    simulate(new RandomPickCompareLoadBalancerStrategy());
  }

  private static void simulate(LoadBalancerStrategy strategy) {
    System.out.println();
    System.out.println("Starting simulation using load balancing strategy=" + strategy.getClass().getSimpleName());

    final LoadBalancer loadBalancer = new LoadBalancer(strategy);
    // 20 processors: 10 processors of 50 capacity, 5 - of 100 capacity and 5 - of 200 capacity
    // overall capacity = 2000
    loadBalancer.addProcessors(10, 50).addProcessors(5, 100).addProcessors(5, 200);

    // feed 1000 units of work five times
    feedUnitsOfWorkAndReport(loadBalancer, 1000, 5);

    // feed zero units of work (should burn down some or (ideally) all units of work)
    feedUnitsOfWorkAndReport(loadBalancer, 0, 1);

    // feed 2000 units of work five times
    feedUnitsOfWorkAndReport(loadBalancer, 2000, 5);

    // feed 3000 units of work one time
    feedUnitsOfWorkAndReport(loadBalancer, 3000, 1);

    // feed zero units of work (should burn down (ideally) all units of work)
    feedUnitsOfWorkAndReport(loadBalancer, 0, 2);

    System.out.println("End of simulation, strategy=" + strategy.getClass().getSimpleName());
    System.out.println("---");
  }

  private static void feedUnitsOfWorkAndReport(LoadBalancer loadBalancer, int unitsOfWork, int times) {
    for (int i = 0; i < times; ++i) {
      loadBalancer.feed(unitsOfWork);
      System.out.println(String.format("Feeding %d units of work. " +
              "Load: p100=%.1f%%, p99=%.1f%%, p90=%.1f%%, p50=%.1f%%",
          unitsOfWork,
          loadBalancer.getOverallLoad(1.0) * 100,
          loadBalancer.getOverallLoad(0.99) * 100,
          loadBalancer.getOverallLoad(0.9) * 100,
          loadBalancer.getOverallLoad(0.5) * 100));

      loadBalancer.process();
    }
  }
}
