package problems.gremlin;

import com.google.common.util.concurrent.Uninterruptibles;
import lombok.experimental.UtilityClass;
import lombok.val;
import problems.gremlin.control.DecisionProvider;

import java.lang.reflect.Proxy;
import java.util.concurrent.TimeUnit;

/**
 * Helper class for applying grem
 */
@UtilityClass
public class GremlinAdapter {

  public static <I, S extends I> I create(S obj, Class<I> targetInterface, DecisionProvider decisionProvider) {
    return targetInterface.cast(Proxy.newProxyInstance(
        targetInterface.getClassLoader(),
        new Class[]{targetInterface},
        (proxy, method, args) -> {
          val decision = decisionProvider.decide(obj, method, args);
          if (decision.isFailBefore()) {
            throw new RuntimeException("Failing " + method + " before execution");
          }
          if (decision.getDelayBeforeMillis() > 0) {
            //noinspection UnstableApiUsage
            Uninterruptibles.sleepUninterruptibly(decision.getDelayBeforeMillis(), TimeUnit.MILLISECONDS);
          }
          val result = method.invoke(obj, args);
          if (decision.isFailAfter()) {
            throw new RuntimeException("Failing " + method + " after execution");
          }
          if (decision.getDelayAfterMillis() > 0) {
            //noinspection UnstableApiUsage
            Uninterruptibles.sleepUninterruptibly(decision.getDelayAfterMillis(), TimeUnit.MILLISECONDS);
          }
          return result;
        }));
  }
}
