package problems.learning.decisiontree.cart.classifier;

import lombok.AllArgsConstructor;
import lombok.Getter;

import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;

/**
 * A leaf node classifies the data.
 * It holds a map of a class (e.g. Apple) to a number of items it
 * appears in the rows from the training datasets that reach this leaf.
 */
@AllArgsConstructor
@Getter
final class LeafNode implements Node {
  private Map<Object, Integer> predictions;

  @Override
  public Node classify(Features features) {
    return this;
  }

  @Override
  public String toString() {
    return predictions.toString();
  }

  @Override
  public String toReadableClassification() {
    final Map<Object, Integer> predictions = getPredictions();
    final double total = predictions.values().stream().reduce(0, (a, b) -> a+b);
    final List<String> probabilities = new ArrayList<>(predictions.size());
    final NumberFormat format = NumberFormat.getPercentInstance(Locale.ROOT);
    for (final Map.Entry<Object, Integer> entry : predictions.entrySet()) {
      probabilities.add(String.format("{%s: %s}",
          entry.getKey(),
          format.format(entry.getValue() / total)));
    }
    return probabilities.toString();
  }
}
