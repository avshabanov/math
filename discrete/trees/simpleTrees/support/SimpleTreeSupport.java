package support;

/**
 * Provides simple tree classes as well as some basic printing support.
 *
 * @author Alexander Shabanov
 */
public abstract class SimpleTreeSupport extends BaseTreeSupport {

  protected static final class Node extends AbstractNode<Node> {
    public Node(int value, Node left, Node right) {
      super(value, left, right);
    }

    @Override
    protected void onSetChild(Node child) { /* do nothing */ }
  }

  //
  // Tree structure
  //

  protected static Node treeFromArray(int... values) {
    return createTreeFromValues(value -> new Node(value, null, null), values);
  }

  protected static Node n(int value, Node left, Node right) {
    return new Node(value, left, right);
  }

  protected static Node n(int value) {
    return n(value, null, null);
  }
}
