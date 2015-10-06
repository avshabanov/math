package com.alexshabanov.simulation.loadBalancing.logic;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;

/**
 * Simulates load balancer. See methods {@link #feed(int)}, {@link #process()} and {@link #getOverallLoad(double)}.
 *
 * @author Alexander Shabanov
 */
public final class LoadBalancer {
  private final List<Processor> processors = new ArrayList<>();
  private final LoadBalancerStrategy balancerStrategy;

  public LoadBalancer(LoadBalancerStrategy balancerStrategy) {
    this.balancerStrategy = Objects.requireNonNull(balancerStrategy);
  }

  public LoadBalancer addProcessors(int count, int processorCapacity) {
    for (int i = 0; i < count; ++i) {
      processors.add(new Processor(processorCapacity));
    }
    return this;
  }

  /**
   * Submits given amount of work to the processors, behind this load balancer.
   *
   * @param unitsToProcess Count of units of work to feed
   */
  public void feed(int unitsToProcess) {
    balancerStrategy.distributeLoad(processors, unitsToProcess);
  }

  /**
   * Executes processors to burn down amount of work
   */
  public void process() {
    processors.forEach(Processor::process);
  }

  /**
   * Returns an overall load to the processors behind this load balancers.
   *
   * E.g. if this methods return 0.75 for percentile=0.99 it means, that 99% of the processors have load which
   * is equal or less than 75%.
   *
   * @param percentile A value from 0 to 1.0, that identifies percentile (e.g. 99 percentile is 0.99)
   * @return A load to the processors, in percents (a value from 0 to 1) for hosts in a given percentile
   */
  public double getOverallLoad(double percentile) {
    final double[] load = new double[processors.size()];
    for (int i = 0; i < load.length; ++i) {
      final Processor processor = processors.get(i);
      load[i] = ((double) processor.getUnitsOfWork()) / processor.getProcessingCapacity();
    }
    Arrays.sort(load);
    return load[(int) (percentile * (load.length - 1))];
  }
}
