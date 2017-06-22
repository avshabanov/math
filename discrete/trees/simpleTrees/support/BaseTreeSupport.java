package support;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.function.Supplier;

/**
 * @author Alexander Shabanov
 */
public abstract class BaseTreeSupport {

  private static <N extends INode<N, V>, V> void addToList(INode<N, V> node, List<V> result) {
    if (node == null) {
      return;
    }

    addToList(node.getLeft(), result);
    result.add(node.getValue());
    addToList(node.getRight(), result);
  }

  protected interface INode<N extends INode, V> {
    V getValue();
    N getSelf();
    N getLeft();
    N getRight();
    void setLeft(N left);
    void setRight(N right);

    @SuppressWarnings("unchecked")
    default N lookupByValue(V value, Comparator<V> comparator, Supplier<N> defaultNodeSupplier) {
      N n = getSelf();
      do {
        final V nodeValue = (V) n.getValue();
        final int r = comparator.compare(nodeValue, value);
        if (r == 0) {
          return n;
        } else if (r < 0) {
          n = (N) n.getRight();
        } else {
          n = (N) n.getLeft();
        }
      } while (n != null);

      return defaultNodeSupplier.get();
    }

    default N lookupByValue(V value, Comparator<V> comparator) {
      return lookupByValue(value, comparator, () -> {
        throw new IllegalStateException("There is no node with value=" + value);
      });
    }

    default List<V> toList() {
      final List<V> result = new ArrayList<>();
      //noinspection unchecked
      addToList(this, result);
      return result;
    }
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
