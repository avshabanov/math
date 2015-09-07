package support;

/**
 * Provides simple tree classes as well as some basic printing support.
 *
 * @author Alexander Shabanov
 */
public abstract class SimpleTreeSupport {

  protected static class Node {
    final int value;
    final Node left;
    final Node right;

    public Node(int value, Node left, Node right) {
      this.value = value;
      this.left = left;
      this.right = right;
    }

    public int getValue() {
      return value;
    }

    public Node getLeft() {
      return left;
    }

    public Node getRight() {
      return right;
    }
  }

  protected static String asString(Node node) {
    final StringBuilder result = new StringBuilder(200);
    printNode(0, node, result);
    return result.toString();
  }

  // strinify helper

  protected static void printNode(int indent, Node node, StringBuilder builder) {
    if (node == null) {
      return;
    }

    printNode(indent + 2, node.left, builder);

    for (int i = 0; i < indent; ++i) {
      builder.append(' ');
    }
    builder.append(node.value).append('\n');

    printNode(indent + 2, node.right, builder);
  }

  //
  // Tree structure
  //

  protected static Node n(int value, Node left, Node right) {
    return new Node(value, left, right);
  }

  protected static Node n(int value) {
    return n(value, null, null);
  }
}
