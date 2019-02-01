package problems.learning.decisiontree.cart.classifier;

import com.google.common.collect.ImmutableList;
import lombok.*;

import java.util.*;

/**
 * Illustrates simplest form of CART learning.
 * This is an adaptation of https://github.com/random-forests/tutorials/blob/master/decision_tree.ipynb
 *
 * Advantages of CART:
 * <ul>
 *   <li>Simple to understand</li>
 *   <li>Variable screening of feature selection</li>
 *   <li>Little effort for data presentation</li>
 * </ul>
 *
 * Disadvantages:
 * <ul>
 *   <li>Tendency to overfitting</li>
 *   <li>Tendency to variance (instability due to small variations)</li>
 * </ul>
 *
 * Important takeaways:
 * <ul>
 *   <li>Greedy algorithms can't guarantee to return the globally optimal decision tree</li>
 *   <li>Create multiple trees to avoid bias</li>
 * </ul>
 *
 * Types:
 * <ul>
 *   <li>Classification trees - when dependenct variable is categorical
 *   </li>
 *   <li>Regression trees - when dependent variable is continuous
 *      <p>Regression - use mean/average</p>
 *   </li>
 * </ul>
 *
 * See also "Let's Write a Decision Tree Classifier from Scratch - Machine Learning Recipes #8"
 *
 * CART preview:
 * <ul>
 *   <li>It starts with a root node for the tree</li>
 *   <li>All nodes receive list of rows as the input</li>
 *   <li>Root will receive the entire training set</li>
 *   <li>Each node will ask a true/false question about one of the features;
 *   In response we partition the data into two subsets.
 *   </li>
 *   <li>These subsets then become the input to two child nodes added to the tree.</li>
 *   <li>The goal is to unmix the labels as we proceed down; or to produce the purest
 *   possible distribution of the labels at each node.
 *   </li>
 *   <li>The trick to building an effective tree is to understand which questions to ask and when;
 *   to do that, we need to quantify how much a question helps to unmix the labels.</li>
 *   <li>A metric called 'Gini impurity' can help to quantify the level of uncertainty at each node.</li>
 *   <li>And quantifying how much questions will reduce that uncertainty using a concept called
 *   'Information Gain'.</li>
 *   <li>Improve the tree until there are no further questions to ask, at which point a leaf is added to the tree</li>
 * </ul>
 *
 * More on questions:
 * <ul>
 *   <li>To generate list of questions, itearte over every value for every value for every feature that appear in
 *   those rows</li>
 *   <li>Each will be a candidate to partition the data</li>
 * </ul>
 *
 * More topics:
 * <ul>
 *   <li>Pruning</li>
 *   <li>Handling missing data</li>
 *   <li>Building trees for regression</li>
 *   <li>Using trees to explore datasets</li>
 * </ul>
 */
public final class CartLearning {

  //
  // Dataset Model
  //

  private static final List<TrainingData> DATASET1 = ImmutableList.of(
      FruitTrainingData.of(Color.GREEN, 3, Fruit.APPLE),
      FruitTrainingData.of(Color.YELLOW, 3, Fruit.APPLE),
      FruitTrainingData.of(Color.RED, 1, Fruit.GRAPE),
      FruitTrainingData.of(Color.RED, 1, Fruit.GRAPE),
      FruitTrainingData.of(Color.YELLOW, 3, Fruit.LEMON)
  );

  private static final FruitTrainingData PROTOTYPE = FruitTrainingData.of(Color.GREEN, 1, Fruit.GRAPE);

  //
  // Demos
  //

  public static final class Demo1 {
    public static void main(String[] args) {
      Question q = Question.of(0, Color.RED);
      System.out.println("question=" + q.toString(PROTOTYPE));
      Partition p = Partition.run(DATASET1, q);
      System.out.println("partition=" + p);

      System.out.println("question(2)=" + Question.of(1, 3).toString(PROTOTYPE));

      // Gini demo
      System.out.println("noMixing gini=" + Cart.calcGini(ImmutableList.of(
          FruitTrainingData.of(Color.YELLOW, 3, Fruit.APPLE),
          FruitTrainingData.of(Color.YELLOW, 3, Fruit.APPLE)
      )));

      System.out.println("someMixing gini=" + Cart.calcGini(ImmutableList.of(
          FruitTrainingData.of(Color.YELLOW, 3, Fruit.APPLE),
          FruitTrainingData.of(Color.RED, 1, Fruit.GRAPE)
      )));

      System.out.println("lotsOfMixing gini=" + Cart.calcGini(ImmutableList.of(
          FruitTrainingData.of(Color.YELLOW, 3, Fruit.APPLE),
          FruitTrainingData.of(Color.RED, 1, Fruit.GRAPE),
          FruitTrainingData.of(Color.BLUE, 1, Fruit.BLUEBERRY),
          FruitTrainingData.of(Color.ORANGE, 4, Fruit.GRAPEFRUIT),
          FruitTrainingData.of(Color.YELLOW, 3, Fruit.LEMON)
      )));

      final double currentUncertainty = Cart.calcGini(DATASET1);
      System.out.println("currentUncertainty=" + currentUncertainty);

      p = Partition.run(DATASET1, Question.of(0, Color.GREEN));
      System.out.println("GREEN infoGain=" + Cart.calcInfoGain(p.getTrueRows(), p.getFalseRows(),
          currentUncertainty));

      p = Partition.run(DATASET1, Question.of(0, Color.RED));
      System.out.println("RED infoGain=" + Cart.calcInfoGain(p.getTrueRows(), p.getFalseRows(),
          currentUncertainty));
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      final Node tree = Cart.buildTree(DATASET1);
      final StringBuilder sb = new StringBuilder();
      Node.print(sb, tree, PROTOTYPE, " ");
      System.out.println(sb.toString());
    }
  }
}

final class Cart {
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
        final Question question = Question.of(col, val);

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

@Value(staticConstructor = "of")
final class Split {
  private double gain;
  private Question question;
}

@Value(staticConstructor = "of")
final class Question {
  private int number; // column number
  private Object value; // column value

  public boolean match(TrainingData trainingData) {
    final Object feature = trainingData.getFeature(number);
    if (feature instanceof Integer) {
      // special case for matching integers
      final Integer featureInt = (Integer) feature;
      final Integer valueInt = (Integer) value;
      return featureInt >= valueInt;
    }
    return Objects.equals(feature, getValue());
  }

  public String toString(TrainingData prototype) {
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

interface Node {

  static void print(StringBuilder sb, Node n, TrainingData prototype, String indent) {
    if (n instanceof LeafNode) {
      sb.append(indent).append("Predict: {");
      boolean next = false;
      for (final Map.Entry<Object, Integer> entry : ((LeafNode) n).getPredictions().entrySet()) {
        if (next) {
          sb.append(", ");
        }
        next = true;
        sb.append(entry.getKey()).append(": ").append(entry.getValue());
      }
      sb.append("}\n");
    } else if (n instanceof DecisionNode) {
      final DecisionNode dn = (DecisionNode) n;
      sb.append(indent).append(dn.getQuestion().toString(prototype)).append("\n");
      sb.append(indent).append("--> True:\n");
      print(sb, dn.getTrueBranch(), prototype, indent + indent);
      sb.append(indent).append("--> False:\n");
      print(sb, dn.getFalseBranch(), prototype, indent + indent);
    } else {
      sb.append("<unknown>\n");
    }
  }
}

/**
 * A decision node asks a question.
 */
@Value
final class DecisionNode implements Node {
  private Question question;
  private Node trueBranch;
  private Node falseBranch;
}

/**
 * A leaf node classifies the data.
 * It holds a map of a class (e.g. Apple) to a number of items it
 * appears in the rows from the training datasets that reach this leaf.
 */
@Value
final class LeafNode implements Node {
  private Map<Object, Integer> predictions;
}

@Value(staticConstructor = "of")
final class Partition {
  private List<TrainingData> trueRows;
  private List<TrainingData> falseRows;

  public static Partition run(List<TrainingData> rows, Question question) {
    final List<TrainingData> trueRows = new ArrayList<>(rows.size());
    final List<TrainingData> falseRows = new ArrayList<>(rows.size());

    for (final TrainingData row : rows) {
      if (question.match(row)) {
        trueRows.add(row);
      } else {
        falseRows.add(row);
      }
    }

    return of(trueRows, falseRows);
  }
}

interface TrainingData {
  String getFeatureName(int column);
  Object getFeature(int column);
  int getFeatureCount();
  Object getLabel();
}

//
// Particular data set:
//

enum Fruit {
  APPLE,
  BLUEBERRY,
  GRAPE,
  GRAPEFRUIT,
  LEMON,
}

enum Color {
  RED,
  ORANGE,
  YELLOW,
  GREEN,
  BLUE
}

@Value(staticConstructor = "of")
final class FruitTrainingData implements TrainingData {
  // feature 1
  private Color color;

  // feature 2
  private int size;

  // label
  private Fruit type;

  @Override
  public String getFeatureName(int column) {
    switch (column) {
      case 0:
        return "color";
      case 1:
        return "size";
      default:
        throw new IllegalArgumentException("Unknown column=" + column);
    }
  }

  @Override
  public Object getFeature(int column) {
    switch (column) {
      case 0:
        return color;
      case 1:
        return size;
      default:
        throw new IllegalArgumentException("Unknown column=" + column);
    }
  }

  @Override
  public int getFeatureCount() {
    return 2;
  }

  @Override
  public Object getLabel() {
    return type;
  }
}
