package problems.learning.decisiontree.cart.classifier;

import lombok.Value;
import lombok.experimental.UtilityClass;

import java.util.Objects;

/**
 * Utility class for questions-related operation.
 */
@UtilityClass
public final class Questions {
  public static Question of(int number, Object value) {
    return new BasicQuestion(number, value);
  }

  @Value
  static final class BasicQuestion implements Question {
    private int number; // column number
    private Object value; // column value

    public boolean match(Features features) {
      final Object feature = features.getFeature(number);
      if (feature instanceof Integer) {
        // special case for matching integers
        final Integer featureInt = (Integer) feature;
        final Integer valueInt = (Integer) value;
        return featureInt >= valueInt;
      }
      return Objects.equals(feature, getValue());
    }

    public String toString(Features prototype) {
      final StringBuilder sb = new StringBuilder();
      sb.append("Is ").append(prototype.getFeatureName(number)).append(" ");
      if (value instanceof Integer) {
        sb.append(">=");
      } else {
        sb.append("==");
      }
      sb.append(' ').append(value).append('?');
      return sb.toString();
    }
  }

  /*@Getter
abstract class AbstractQuestion implements Question {
  protected final int number; // column number

  protected AbstractQuestion(int number) {
    this.number = number;
  }
}

final class ExactMatchQuestion extends AbstractQuestion {
  private final Object value;

  protected ExactMatchQuestion(int number, Object value) {
    super(number);
    this.value = value;
  }

  @Override
  public boolean match(Features features) {
    final Object feature = features.getFeature(number);
    return Objects.equals(feature, value);
  }

  @Override
  public String toString(Features prototype) {
    return "Is " + prototype.getFeatureName(number) + " == " + value + "?";
  }
}

final class IntQuestion extends AbstractQuestion {
  private final int value;
}*/
}
