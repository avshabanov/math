package problems.learning.decisiontree.cart.classifier;

/**
 * Represents features of the training row or input dataset.
 */
public interface Features {
  String getFeatureName(int column);
  Object getFeature(int column);
  int getFeatureCount();
}
