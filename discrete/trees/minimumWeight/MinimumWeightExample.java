import support.SimpleTreeSupport;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * Sample run:
 * <pre>
 * Min weight=55 for elements=[10, 11, 12], tree:
 *   10
 * 11
 *   12
 *
 * Min weight=343 for elements=[1, 20, 300], tree:
 *     1
 *   20
 * 300
 *
 * Min weight=145 for elements=[1, 2, 3, 4, 5, 6, 7, 8, 9, 10], tree:
 *         1
 *       2
 *     3
 *       4
 *   5
 *     6
 * 7
 *     8
 *   9
 *     10
 * </pre>
 *
 */
public final class MinimumWeightExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(Arrays.asList(10, 11, 12));
    demo(Arrays.asList(1, 20, 300));
    demo(Arrays.asList(1, 2, 3, 4, 5, 6, 7, 8, 9, 10));
  }

  public static void demo(List<Integer> elements) {
    final Result result = findMinWeight(elements);
    System.out.println("Min weight=" + result.getWeight() +
        " for elements=" + elements + ", tree:\n" + asString(result.getNode()));
  }

  public static Result findMinWeight(List<Integer> elements) {
    final Finder finder = new Finder(elements);
    return finder.find(1, 0, elements.size());
  }

  private static final class Finder {
    private final List<Integer> input;

    public Finder(List<Integer> input) {
      this.input = new ArrayList<>(input);
      Collections.sort(this.input);
    }

    public Result find(int currentLevel, int leftPos, int rightPos) {
      int minWeight = Integer.MAX_VALUE;
      Node node = null;
      for (int i = leftPos; i < rightPos; ++i) {
        final Result leftResult = find(currentLevel + 1, leftPos, i);
        final Result rightResult = find(currentLevel + 1, i + 1, rightPos);
        final int value = input.get(i);
        final int weight = value * currentLevel + leftResult.getWeight() + rightResult.getWeight();
        if (weight < minWeight) {
          minWeight = weight;
          node = new Node(value, leftResult.getNode(), rightResult.getNode());
        }
      }
      return node == null ? EMPTY_RESULT : new MaterialResult(minWeight, node);
    }
  }

  private interface Result {
    int getWeight();
    Node getNode();
  }

  private static final Result EMPTY_RESULT = new Result() {

    @Override
    public int getWeight() {
      return 0;
    }

    @Override
    public Node getNode() {
      return null;
    }
  };

  private static final class MaterialResult implements Result {
    private final int weight;
    private final Node node;

    public MaterialResult(int weight, Node node) {
      this.weight = weight;
      this.node = node;
    }

    @Override
    public int getWeight() {
      return weight;
    }

    @Override
    public Node getNode() {
      return node;
    }
  }
}
