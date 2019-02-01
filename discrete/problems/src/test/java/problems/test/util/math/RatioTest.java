package problems.test.util.math;

import org.junit.Test;
import problems.util.math.Ratio;

import static org.junit.Assert.assertEquals;

/**
 * Tests {@link problems.util.math.Ratio} class.
 */
public final class RatioTest {
  private static final double EPSILON = 0.0001;

  @Test
  public void shouldMakeRatiosOfDistinctValuesTheSame() {
    assertEquals(Ratio.of(-3, 2), Ratio.of(3, -2));
  }

  @Test
  public void shouldNormalizeNegativeNumeratorAndDenominator() {
    assertEquals(Ratio.of(-3, -2), Ratio.of(3, 2));
  }

  @Test
  public void shouldSimplifyToInteger() {
    assertEquals(Ratio.of(4, 2), Ratio.fromInteger(2));
  }

  @Test
  public void shouldShouldYieldCorrectIntValue() {
    assertEquals(Ratio.fromInteger(2).intValue(), 2);
  }

  @Test
  public void shouldYieldRightDoubleValue() {
    assertEquals(Ratio.of(6, 14).doubleValue(), 3.0 / 7, EPSILON);
  }
}
