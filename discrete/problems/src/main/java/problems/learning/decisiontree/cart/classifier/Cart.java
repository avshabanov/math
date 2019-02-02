package problems.learning.decisiontree.cart.classifier;

import lombok.experimental.UtilityClass;

import java.util.*;

/**
 * Utility class that encapsulates CART algorithm.
 */
@UtilityClass
public class Cart {
  /**
   * Calculates gini impurity for a given list of rows.
   * See also https://en.wikipedia.org/wiki/Decision_tree_learning#Gini_impurity
   *
   * @param rows List of rows
   * @return Gini impurity
   */
  public static double calcGini(List<TrainingData> rows) {
    double impurity = 1.0;
    Map<Object, Integer> counts = classCounts(rows);

    for (Map.Entry<Object, Integer> entry : counts.entrySet()) {
      final double probabilityOfLabel = entry.getValue() / ((double) rows.size());
      impurity -= Math.pow(probabilityOfLabel, 2);
    }
    return impurity;
  }

  /**
   * Finds the best question to ask by iterating over every feature / value and calculating
   * the information gain.
   *
   * The best question is a question that reduces the uncertainty the most.
   *
   * @param rows Training data set
   * @return Best split
   */
  public static Split findBestSplit(List<TrainingData> rows) {
    double bestGain = 0.0; // keep track of the best information gain
    Question bestQuestion = null; // keep track of the feature / value that produced it
    double currentUncertainty = calcGini(rows);
    int numberOfFeatures = rows.get(0).getFeatureCount();

    for (int col = 0; col < numberOfFeatures; ++col) {
      final Set<Object> values = new HashSet<>();
      for (TrainingData td : rows) {
        values.add(td.getFeature(col));
      }

      for (final Object val : values) {
        final Question question = Questions.of(col, val);

        // try splitting the dataset
        final Partition partition = Partition.run(rows, question);

        // skip this split if it doesn't divide the dataset
        if (partition.getTrueRows().isEmpty() || partition.getFalseRows().isEmpty()) {
          continue;
        }

        // calculate the information gain from this split
        final double gain = calcInfoGain(partition.getTrueRows(), partition.getFalseRows(), currentUncertainty);

        if (gain >= bestGain) {
          bestGain = gain;
          bestQuestion = question;
        }
      }
    }

    return Split.of(bestGain, bestQuestion);
  }

  /**
   * Calculates information gain or the uncertainty of the starting node minus the weighted impurity of
   * two child nodes.
   *
   * @param left Left node split
   * @param right Right node split
   * @param uncertainty Current uncertainty
   * @return Information gain
   */
  public static double calcInfoGain(List<TrainingData> left, List<TrainingData> right, double uncertainty) {
    final double p = ((double) left.size() / (double) (left.size() + right.size()));
    return uncertainty - p * calcGini(left) - (1 - p) * calcGini(right);
  }

  /**
   * Counts the number of each type of example in a dataset.
   *
   * @param rows Rows
   * @return A map of label -> count
   */
  public static Map<Object, Integer> classCounts(List<TrainingData> rows) {
    final Map<Object, Integer> counts = new HashMap<>();

    for (final TrainingData row : rows) {
      final Object label = row.getLabel();
      final Integer currentCount = counts.get(label);
      counts.put(label, 1 + (currentCount != null ? currentCount : 0));
    }

    return counts;
  }

  /**
   * Builds the tree
   *
   * @param rows Training data set
   * @return Tree
   */
  public static Node buildTree(List<TrainingData> rows) {
    // try partitioning the dataset on each of the unique attribute,
    // calculate the information gain,
    // and return the question that produces the highest gain
    Split split = findBestSplit(rows);

    // base case: no further info gain, since we can ask no further
    // question, we'll return a leaf
    if (split.getGain() == 0) {
      return new LeafNode(classCounts(rows));
    }

    // we found a useful feature / value to partition on
    final Partition p = Partition.run(rows, split.getQuestion());

    // recursively build the branches
    Node trueBranch = buildTree(p.getTrueRows());
    Node falseBranch = buildTree(p.getFalseRows());

    return new DecisionNode(split.getQuestion(), trueBranch, falseBranch);
  }
}
