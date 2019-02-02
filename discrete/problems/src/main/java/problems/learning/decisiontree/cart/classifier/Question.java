package problems.learning.decisiontree.cart.classifier;

/**
 * Represents question abstration.
 */
public interface Question {

  boolean match(Features features);

  String toString(Features prototype);
}
