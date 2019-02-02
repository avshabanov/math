package problems.learning.decisiontree.cart.classifier;

import java.util.Arrays;
import java.util.Objects;

/**
 * Array-based learning features.
 */
public final class ArrayFeatures implements Features {
  private final Object[] values;

  ArrayFeatures(Object[] values) {
    values = Objects.requireNonNull(values);
    this.values = Arrays.copyOf(values, values.length);
  }

  public static Features of(TrainingData trainingData) {
    final Object[] values = new Object[trainingData.getFeatureCount()];
    for (int i = 0; i < trainingData.getFeatureCount(); ++i) {
      values[i] = trainingData.getFeature(i);
    }
    return of(values);
  }

  public static Features of(Object... values) {
    return new ArrayFeatures(values);
  }

  @Override
  public String getFeatureName(int column) {
    return "#" + column;
  }

  @Override
  public Object getFeature(int column) {
    return values[column];
  }

  @Override
  public int getFeatureCount() {
    return values.length;
  }

  @Override
  public String toString() {
    return Arrays.toString(values);
  }
}
