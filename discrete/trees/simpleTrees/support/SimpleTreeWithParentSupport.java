package support;

/**
 * Provides simple tree classes as well as some basic printing support.
 *
 * @author Alexander Shabanov
 */
public abstract class SimpleTreeWithParentSupport extends BaseTreeSupport {

  protected static final class Node extends AbstractNode<Node> {
    private Node parent;

    public Node(int value, Node left, Node right) {
      super(value, left, right);
    }

    public Node getParent() {
      return parent;
    }

    public void setParent(Node parent) {
      this.parent = parent;
    }

    @Override
    protected void onSetChild(Node child) {
      child.setParent(this);
    }
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
