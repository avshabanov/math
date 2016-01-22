package support;

import java.util.Arrays;

/**
 * Provides simple tree classes as well as some basic printing support.
 *
 * @author Alexander Shabanov
 */
public abstract class SimpleTreeSupport {

  protected interface INode<N extends INode> {
    int getValue();
    N getLeft();
    N getRight();
    void setLeft(N left);
    void setRight(N left);
  }

  protected static abstract class AbstractNode<N extends INode> implements INode<N> {
    private final int value;
    private N left;
    private N right;

    protected AbstractNode(int value, N left, N right) {
      this.value = value;
      this.left = left;
      this.right = right;
    }

    @Override
    public int getValue() {
      return value;
    }

    @Override
    public N getLeft() {
      return left;
    }

    @Override
    public N getRight() {
      return right;
    }

    @Override
    public void setLeft(N left) {
      this.left = left;
    }

    @Override
    public void setRight(N right) {
      this.right = right;
    }

    public String toString() {
      return asSinglelineString(this);
    }
  }

  protected static final class Node extends AbstractNode<Node> {
    public Node(int value, Node left, Node right) {
      super(value, left, right);
    }
  }

  protected static String asSinglelineString(INode<?> node) {
    return "(v: " + node.getValue() +
        (node.getLeft() != null ? ", left: " + asSinglelineString(node.getLeft()) : "") +
        (node.getRight() != null ? ", right: " + asSinglelineString(node.getRight()) : "") +
        ')';
  }

  protected static String asString(INode<?> node) {
    if (node == null) {
      return "(null)";
    }

    final StringBuilder result = new StringBuilder(200);
    printNode(0, node, result);
    return result.toString();
  }

  // stringify helper

  protected static void printNode(int indent, INode<?> node, StringBuilder builder) {
    if (node == null) {
      return;
    }

    printNode(indent + 2, node.getLeft(), builder);

    for (int i = 0; i < indent; ++i) {
      builder.append(' ');
    }
    builder.append(node.getValue()).append('\n');

    printNode(indent + 2, node.getRight(), builder);
  }

  //
  // Tree structure
  //

  protected static Node treeFromArray(int... values) {
    Node root = null;
    for (final int value : values) {
      if (root == null) {
        root = new Node(value, null, null);
      } else {
        // lookup for insertion place and put this value
        Node node = root;
        for (;;) {
          if (value < node.getValue()) {
            // goto left subtree
            if (node.getLeft() != null) {
              node = node.getLeft();
            } else {
              node.setLeft(new Node(value, null, null)); // parent=node
              break;
            }
          } else if (value > node.getValue()) {
            // goto right subtree
            if (node.getRight() != null) {
              node = node.getRight();
            } else {
              node.setRight(new Node(value, null, null)); // parent=node
              break;
            }
          } else {
            throw new IllegalArgumentException("Duplicate value=" + value + " in array=" + Arrays.toString(values));
          }
        }
      }
    }
    return root;
  }

  protected static Node n(int value, Node left, Node right) {
    return new Node(value, left, right);
  }

  protected static Node n(int value) {
    return n(value, null, null);
  }
}
