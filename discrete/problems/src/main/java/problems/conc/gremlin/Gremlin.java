package problems.conc.gremlin;

import lombok.Builder;
import lombok.NonNull;
import lombok.Value;
import lombok.experimental.UtilityClass;

import java.util.concurrent.TimeUnit;

/**
 * Utility class for gremlin API.
 */
@UtilityClass
public class Gremlin {

  public interface GremlinNode {

    void die(@NonNull TriggerCondition when);

    void silence(@NonNull TriggerCondition until);

    void setResponseDelay(@NonNull TimedJitter timeMillis);
  }

  @Value
  @Builder
  public static class TimedJitter {

    long baseTime;

    long jitterDelay;

    @Builder.Default
    TimeUnit timeUnit = TimeUnit.MILLISECONDS;
  }

  @Value
  @Builder
  public static class TriggerCondition {

    long timeout;

    @Builder.Default
    TimeUnit timeUnit = TimeUnit.MILLISECONDS;
  }
}
