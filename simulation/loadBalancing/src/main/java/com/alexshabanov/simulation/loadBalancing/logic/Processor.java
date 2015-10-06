package com.alexshabanov.simulation.loadBalancing.logic;

/**
 * Emulates processor (load balancer distributes the load across processors).
 *
 * @author Alexander Shabanov
 */
public final class Processor {
  private int unitsOfWork = 0;
  private final int processingCapacity;

  public Processor(int processingCapacity) {
    this.processingCapacity = processingCapacity;
  }

  public void addUnitOfWork(int units) {
    this.unitsOfWork += units;
  }

  public void process() {
    unitsOfWork = Math.max(0, unitsOfWork - processingCapacity);
  }

  public int getUnitsOfWork() {
    return unitsOfWork;
  }

  public int getProcessingCapacity() {
    return processingCapacity;
  }

  public double getExpectedLoadForGivenUnitsOfWork(int unitsOfWork) {
    return (getUnitsOfWork() + unitsOfWork) / (double) getProcessingCapacity();
  }
}
