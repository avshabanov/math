package support;

import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

/**
 * Provides simple tree classes as well as some basic printing support.
 *
 * @author Alexander Shabanov
 */
public abstract class SimpleTreeSupport extends BaseTreeSupport {

  protected static final class Node extends AbstractNode<Node, Integer> {
    public Node(Integer value, Node left, Node right) {
      super(value);
      setLeft(left);
      setRight(right);
    }

    @Override
    public Node getSelf() { return this; }

    @Override
    protected void onSetChild(Node child) { /* do nothing */ }
  }

  protected static Node randomTree(Stream<Integer> valueStream, Random random) {
    final List<Integer> values = valueStream.collect(Collectors.toList());
    final List<Integer> shuffledValues = IntStream.range(0, values.size())
            .map((i) -> values.remove(random.nextInt(values.size())))
            .boxed().collect(Collectors.toList());
    return treeFromArray(shuffledValues.toArray(new Integer[shuffledValues.size()]));
  }

  //
  // Tree structure
  //

  protected static Node treeFromArray(Integer... values) {
    return createTreeFromValues(value -> new Node(value, null, null), values);
  }

  protected static Node n(int value, Node left, Node right) {
    return new Node(value, left, right);
  }

  protected static Node n(int value) {
    return n(value, null, null);
  }
}
