package com.alexshabanov.simulation.loadBalancing.logic.strategy;

import com.alexshabanov.simulation.loadBalancing.logic.LoadBalancerStrategy;
import com.alexshabanov.simulation.loadBalancing.logic.Processor;

import java.util.*;
import java.util.concurrent.ThreadLocalRandom;

/**
 * Represents load balancing strategy without full knowledge of a system, that tries to implement suboptimal load
 * distribution behavior by picking {@link #PICK_COUNT} number of processors, find processor with the least load
 * between them and submit given amount of work to that processor.
 *
 * @author Alexander Shabanov
 */
public final class RandomPickCompareLoadBalancerStrategy implements LoadBalancerStrategy {
  private static final int PICK_COUNT = 2;
  private final Random random = ThreadLocalRandom.current();

  @Override
  public void distributeLoad(List<Processor> processors, int unitsToProcess) {
    for (int i = 0; i < unitsToProcess; ++i) {
      final List<Processor> randProcessors = getRandomProcessors(processors);
      Processor processor = randProcessors.get(0);
      double minLoaded = processor.getExpectedLoadForGivenUnitsOfWork(1);
      for (int j = 1; j < randProcessors.size(); ++j) {
        final Processor cur = randProcessors.get(j);
        final double curLoad = cur.getExpectedLoadForGivenUnitsOfWork(1);
        if (minLoaded > curLoad) {
          processor = cur;
          minLoaded = curLoad;
        }
      }

      processor.addUnitOfWork(1);
    }
  }

  private List<Processor> getRandomProcessors(List<Processor> processors) {
    assert PICK_COUNT < processors.size();
    final int[] ints = random.ints(0, processors.size()).distinct().limit(PICK_COUNT).toArray();
    final List<Processor> result = new ArrayList<>(PICK_COUNT);
    for (int n : ints) {
      result.add(processors.get(n));
    }
    return result;
  }
}
