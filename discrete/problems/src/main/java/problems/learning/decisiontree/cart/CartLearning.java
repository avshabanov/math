package problems.learning.decisiontree.cart;

import com.google.common.collect.ImmutableList;
import lombok.Value;
import problems.learning.decisiontree.cart.classifier.*;

import java.util.List;

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
 *   <li>Classification trees - when dependent variable is categorical
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
      Question q = Questions.of(0, Color.RED);
      System.out.println("question=" + q.toString(PROTOTYPE));
      Partition p = Partition.run(DATASET1, q);
      System.out.println("partition=" + p);

      System.out.println("question(2)=" + Questions.of(1, 3).toString(PROTOTYPE));

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

      p = Partition.run(DATASET1, Questions.of(0, Color.GREEN));
      System.out.println("GREEN infoGain=" + Cart.calcInfoGain(p.getTrueRows(), p.getFalseRows(),
          currentUncertainty));

      p = Partition.run(DATASET1, Questions.of(0, Color.RED));
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

  public static final class Demo3 {
    public static void main(String[] args) {
      final Node tree = Cart.buildTree(DATASET1);

      Features features = ArrayFeatures.of(DATASET1.get(0));
      Node classification = tree.classify(features);
      System.out.println("classify(" + features + ")=" + classification.toReadableClassification());

      features = ArrayFeatures.of(DATASET1.get(1));
      classification = tree.classify(features);
      System.out.println("classify(" + features + ")=" + classification.toReadableClassification());
    }
  }

  //
  // Helper classes
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
  static final class FruitTrainingData implements TrainingData {
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
}

