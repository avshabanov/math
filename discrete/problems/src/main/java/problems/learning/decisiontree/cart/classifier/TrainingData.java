package problems.learning.decisiontree.cart.classifier;

/**
 * Represents labeled feature row or training data.
 */
public interface TrainingData extends Features {
  Object getLabel();
}
