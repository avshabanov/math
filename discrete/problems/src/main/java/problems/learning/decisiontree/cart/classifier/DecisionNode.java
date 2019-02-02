package problems.learning.decisiontree.cart.classifier;

import lombok.Value;

/**
 * A decision node asks a question.
 */
@Value
public final class DecisionNode implements Node {
  private Question question;
  private Node trueBranch;
  private Node falseBranch;

  @Override
  public Node classify(Features features) {
    if (question.match(features)) {
      return trueBranch.classify(features);
    } else {
      return falseBranch.classify(features);
    }
  }

  @Override
  public String toReadableClassification() {
    return "<unknown>";
  }
}
