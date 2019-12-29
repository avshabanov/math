package problems.gremlin.control;

import java.lang.reflect.Method;

/**
 * TBD
 */
public interface DecisionProvider {

  Decision decide(Object source, Method method, Object[] args);
}
