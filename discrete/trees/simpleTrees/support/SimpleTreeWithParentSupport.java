package support;

/**
 * Provides simple tree classes as well as some basic printing support.
 *
 * @author Alexander Shabanov
 */
public abstract class SimpleTreeWithParentSupport extends BaseTreeSupport {

  protected static final class Node extends AbstractNode<Node, Integer> {
    private Node parent;

    public Node(Integer value, Node left, Node right) {
      super(value);
      setLeft(left);
      setRight(right);
    }

    @Override
    public Node getSelf() { return this; }

    public Node getParent() {
      return parent;
    }

    public void setParent(Node parent) {
      this.parent = parent;
    }

    @Override
    protected void onSetChild(Node child) {
      if (child != null) {
        assert child.getParent() == null;
        child.setParent(this);
      }
    }
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
