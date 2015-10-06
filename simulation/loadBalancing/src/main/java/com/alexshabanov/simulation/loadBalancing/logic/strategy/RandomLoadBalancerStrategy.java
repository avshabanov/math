package com.alexshabanov.simulation.loadBalancing.logic.strategy;

import com.alexshabanov.simulation.loadBalancing.logic.LoadBalancerStrategy;
import com.alexshabanov.simulation.loadBalancing.logic.Processor;

import java.util.List;
import java.util.Random;
import java.util.concurrent.ThreadLocalRandom;

/**
 * A load balancing strategy, that picks random processor for each single unit of work.
 *
 * @author Alexander Shabanov
 */
public final class RandomLoadBalancerStrategy implements LoadBalancerStrategy {
  private final Random random = ThreadLocalRandom.current();

  @Override
  public void distributeLoad(List<Processor> processors, int unitsToProcess) {
    for (int i = 0; i < unitsToProcess; ++i) {
      processors.get(random.nextInt(processors.size())).addUnitOfWork(1);
    }
  }
}
