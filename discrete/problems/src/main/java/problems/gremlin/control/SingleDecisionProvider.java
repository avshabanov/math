package problems.gremlin.control;

import java.lang.reflect.Method;

public class SingleDecisionProvider implements DecisionProvider {
  private volatile Decision decision = Decision.builder().build();

  public synchronized void setDecision(Decision decision) {
    this.decision = decision;
  }

  @Override
  public synchronized Decision decide(Object source, Method method, Object[] args) {
    return decision;
  }
}
