package support;

import java.util.Arrays;

/**
 * @author Alexander Shabanov
 */
public abstract class BaseTreeSupport {

  protected interface INode<N extends INode, V> {
    V getValue();
    N getLeft();
    N getRight();
    void setLeft(N left);
    void setRight(N right);
  }

  protected static abstract class AbstractNode<N extends INode, V> implements INode<N, V> {
    private final V value;
    private N left;
    private N right;

    protected AbstractNode(V value) {
      this.value = value;
    }

    @Override
    public V getValue() {
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
      onSetChild(left);
    }

    @Override
    public void setRight(N right) {
      this.right = right;
      onSetChild(right);
    }

    public String toString() {
      return asSinglelineString(this);
    }

    protected abstract void onSetChild(N child);
  }


  protected static String asSinglelineString(INode<?, ?> node) {
    return "(v: " + node.getValue() +
        (node.getLeft() != null ? ", left: " + asSinglelineString(node.getLeft()) : "") +
        (node.getRight() != null ? ", right: " + asSinglelineString(node.getRight()) : "") +
        ')';
  }

  protected static String asString(INode<?, ?> node) {
    if (node == null) {
      return "(null)";
    }

    final StringBuilder result = new StringBuilder(200);
    printNode(0, node, result);
    return result.toString();
  }

  // stringify helper

  protected static void printNode(int indent, INode<?, ?> node, StringBuilder builder) {
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
  // Creation methods
  //

  protected interface INodeCreator<N, V> {
    N create(V value);
  }

  @SafeVarargs
  protected static <V extends Comparable<V>, N extends INode<N, V>> N createTreeFromValues(
          INodeCreator<N, V> creator,
          V... values) {
    N root = null;
    for (final V value : values) {
      if (root == null) {
        root = creator.create(value);
      } else {
        // lookup for insertion place and put this value
        N node = root;
        for (;;) {
          final int comparisonResult = value.compareTo(node.getValue());
          if (comparisonResult < 0) {
            // goto left subtree
            if (node.getLeft() != null) {
              node = node.getLeft();
            } else {
              node.setLeft(creator.create(value)); // parent=node
              break;
            }
          } else if (comparisonResult > 0) {
            // goto right subtree
            if (node.getRight() != null) {
              node = node.getRight();
            } else {
              node.setRight(creator.create(value)); // parent=node
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
}
