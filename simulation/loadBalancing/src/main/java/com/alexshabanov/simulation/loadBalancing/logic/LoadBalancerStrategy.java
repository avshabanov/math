package com.alexshabanov.simulation.loadBalancing.logic;

import java.util.List;

/**
 * Interface to the logic that implements load distribution.
 *
 * @author Alexander Shabanov
 */
public interface LoadBalancerStrategy {
  void distributeLoad(List<Processor> processors, int unitsToProcess);
}
