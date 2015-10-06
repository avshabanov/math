package com.alexshabanov.simulation.loadBalancing.logic.strategy;

import com.alexshabanov.simulation.loadBalancing.logic.LoadBalancerStrategy;
import com.alexshabanov.simulation.loadBalancing.logic.Processor;

import java.util.List;

/**
 * Simulates load balancing strategy that uses the best possible load distribution strategy.
 * The disadvantage of this approach is that it requires load balancer to store information about every processor's
 * which is not always possible.
 *
 * @author Alexander Shabanov
 */
public final class ExactDistributionLoadBalancerStrategy implements LoadBalancerStrategy {

  @Override
  public void distributeLoad(List<Processor> processors, int unitsToProcess) {
    for (int i = 0; i < unitsToProcess; ++i) {
      // send load to the host with the least load
      Processor processor = processors.get(0);
      double minLoaded = processor.getExpectedLoadForGivenUnitsOfWork(1);
      for (int j = 1; j < processors.size(); ++j) {
        final Processor cur = processors.get(j);
        final double curLoad = cur.getExpectedLoadForGivenUnitsOfWork(1);
        if (minLoaded > curLoad) {
          processor = cur;
          minLoaded = curLoad;
        }
      }

      // send this unit of work to the processor with minimum load
      processor.addUnitOfWork(1);
    }
  }
}
