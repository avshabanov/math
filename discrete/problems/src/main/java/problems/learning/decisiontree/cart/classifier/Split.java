package problems.learning.decisiontree.cart.classifier;

import lombok.Value;

/**
 * Represents split data.
 */
@Value(staticConstructor = "of")
public final class Split {
  private double gain;
  private Question question;
}
