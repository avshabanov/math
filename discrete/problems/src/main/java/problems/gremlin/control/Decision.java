package problems.gremlin.control;

import lombok.Builder;
import lombok.Value;

@Value
@Builder
public class Decision {

  @Builder.Default
  long delayBeforeMillis = 1L;

  @Builder.Default
  boolean failBefore = false;

  @Builder.Default
  long delayAfterMillis = 1L;

  @Builder.Default
  boolean failAfter = false;
}
