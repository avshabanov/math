package problems.learning.decisiontree.cart.classifier;

/**
 * Represents decision tree's node.
 */
public interface Node {

  Node classify(Features features);

  default String toReadableClassification() {
    return "<unknown>";
  }

  static void print(StringBuilder sb, Node n, TrainingData prototype, String indent) {
    if (n instanceof LeafNode) {
      sb.append(indent).append("Predict: ").append(n).append("\n");
    } else if (n instanceof DecisionNode) {
      final DecisionNode dn = (DecisionNode) n;
      sb.append(indent).append(dn.getQuestion().toString(prototype)).append("\n");
      sb.append(indent).append("--> True:\n");
      print(sb, dn.getTrueBranch(), prototype, indent + indent);
      sb.append(indent).append("--> False:\n");
      print(sb, dn.getFalseBranch(), prototype, indent + indent);
    } else {
      sb.append("<unknown>\n");
    }
  }
}
