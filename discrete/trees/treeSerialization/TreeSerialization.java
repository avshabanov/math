import support.SimpleTreeSupport;

import java.util.ArrayList;
import java.util.List;

/**
 * Sample output:
 *
 * <code>
 * [ORIGINAL]     tree1=
 *     2
 *   7
 *     9
 * 5
 *     11
 *   8
 *     1
 *
 * [DESERIALIZED] tree1=
 *     2
 *   7
 *     9
 * 5
 *     11
 *   8
 *     1
 *
 * ---
 *
 * [ORIGINAL]     tree2=
 * 5
 *   1
 *     9
 *       17
 *
 * [DESERIALIZED] tree2=
 * 5
 *   1
 *     9
 *       17
 *
 * ---
 *
 * [ORIGINAL]     tree3=
 * 9
 *
 * [DESERIALIZED] tree3=
 * 9
 *
 * ---
 * </code>
 *
 * @author Alexander Shabanov
 */
public class TreeSerialization extends SimpleTreeSupport {

  public static void main(String[] args) {
    // [1]
    final Node tree1 = n(5, n(7, n(2), n(9)), n(8, n(11), n(1)));
    System.out.println("[ORIGINAL]     tree1=\n" + asString(tree1));
    final List<SerializedNode> snl1 = toSerializedForm(tree1);
    System.out.println("[DESERIALIZED] tree1=\n" + asString(fromSerializedForm(snl1)));
    System.out.println("---\n");

    // [2]
    final Node tree2 = n(5, null, n(1, null, n(9, null, n(17))));
    System.out.println("[ORIGINAL]     tree2=\n" + asString(tree2));
    final List<SerializedNode> snl2 = toSerializedForm(tree2);
    System.out.println("[DESERIALIZED] tree2=\n" + asString(fromSerializedForm(snl2)));
    System.out.println("---\n");

    // [3]
    final Node tree3 = n(9);
    System.out.println("[ORIGINAL]     tree3=\n" + asString(tree3));
    final List<SerializedNode> snl3 = toSerializedForm(tree3);
    System.out.println("[DESERIALIZED] tree3=\n" + asString(fromSerializedForm(snl3)));
    System.out.println("---\n");
  }

  //
  // Serialization representation (array of these structures should be serialized as is)
  //

  private static final class SerializedNode {
    int value;
    int leftIndex;
    int rightIndex;
  }

  // serialization

  private static List<SerializedNode> toSerializedForm(Node node) {
    final List<SerializedNode> result = new ArrayList<>();
    putNode(node, result);
    return result;
  }

  // serialization helper

  private static int putNode(Node node, List<SerializedNode> result) {
    if (node == null) {
      return -1;
    }

    final int index = result.size();
    final SerializedNode sn = new SerializedNode();
    sn.value = node.getValue();
    result.add(sn);
    sn.leftIndex = putNode(node.getLeft(), result);
    sn.rightIndex = putNode(node.getRight(), result);
    return index;
  }

  // deserialization

  private static Node fromSerializedForm(List<SerializedNode> serializedNodes) {
    return getNextNode(0, serializedNodes);
  }

  // deserialization helper

  private static Node getNextNode(int index, List<SerializedNode> serializedNodes) {
    if (index == -1) {
      return null;
    }

    final SerializedNode sn = serializedNodes.get(index);
    return new Node(sn.value,
        getNextNode(sn.leftIndex, serializedNodes),
        getNextNode(sn.rightIndex, serializedNodes));
  }
}
