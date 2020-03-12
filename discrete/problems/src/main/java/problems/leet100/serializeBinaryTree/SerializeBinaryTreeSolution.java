package problems.leet100.serializeBinaryTree;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

/**
 * 297. Serialize and Deserialize Binary Tree
 * https://leetcode.com/problems/serialize-and-deserialize-binary-tree/
 * <p>
 * Serialization is the process of converting a data structure or object into a sequence of bits so that it can be
 * stored in a file or memory buffer, or transmitted across a network connection link to be reconstructed later in
 * the same or another computer environment.
 * Design an algorithm to serialize and deserialize a binary tree.
 * There is no restriction on how your serialization/deserialization algorithm should work.
 * You just need to ensure that a binary tree can be serialized to a string and this string can be deserialized to
 * the original tree structure.
 * </p>
 * Submission result:
 * <p>
 * Runtime: 7 ms, faster than 95.15% of Java online submissions for Serialize and Deserialize Binary Tree.
 * Memory Usage: 42.2 MB, less than 16.19% of Java online submissions for Serialize and Deserialize Binary Tree.
 * </p>
 */
public class SerializeBinaryTreeSolution {

  public static void main(String[] args) {
    demo1();
  }

  private static void demo1() {
    final TreeNode[] nodes = IntStream.range(0, 5).mapToObj(i -> new TreeNode(i + 10)).toArray(TreeNode[]::new);
    nodes[0].left = nodes[1];
    nodes[0].right = nodes[3];
    nodes[3].left = nodes[2];
    nodes[3].right = nodes[4];

    final Codec c = new Codec();
    final String s = c.serialize(nodes[0]);
    final TreeNode n = c.deserialize(s);
    System.out.printf("Serialized tree to %s\nSource root:       %s\nDeserialized root: %s\n",
        s, nodes[0], n);
  }

  private static class Codec {
    int serializationIndex;

    // Encodes a tree to a single string.
    public String serialize(TreeNode root) {
      if (root == null) {
        return "";
      }

      this.serializationIndex = 0;
      final StringBuilder b = new StringBuilder(20);
      add(b, root);
      return b.toString();
    }

    private int add(final StringBuilder b, TreeNode n) {
      if (n == null) {
        return -1;
      }

      final int leftIndex = add(b, n.left);
      final int rightIndex = add(b, n.right);

      final int result = serializationIndex;
      ++serializationIndex;

      b.append(n.val).append(',').append(leftIndex).append(',').append(rightIndex).append(';');
      return result;
    }

    // Decodes your encoded data to tree.
    public TreeNode deserialize(String data) {
      if (data.isEmpty()) {
        return null;
      }

      // pre-initialize all the nodes that we're going to return
      final List<TreeNode> nodes = new ArrayList<>();
      for (int i = 0; i < data.length();) {
        int sepIndex = data.indexOf(';', i);
        sepIndex = sepIndex > 0 ? sepIndex : data.length();

        final int i1 = data.indexOf(',', i + 1);
        final int i2 = data.indexOf(',', i1 + 1);
        assert i1 > 0 && i2 > 0 && i2 < sepIndex;

        final int val = Integer.parseInt(data.substring(i, i1));
        final int leftIndex = Integer.parseInt(data.substring(i1 + 1, i2));
        final int rightIndex = Integer.parseInt(data.substring(i2 + 1, sepIndex));

        // insert node
        final TreeNode node = new TreeNode(val);
        node.left = leftIndex < 0 ? null : nodes.get(leftIndex);
        node.right = rightIndex < 0 ? null : nodes.get(rightIndex);
        nodes.add(node);

        i = sepIndex + 1;
      }

      return nodes.get(nodes.size() - 1);
    }
  }

  private static class TreeNode {
    int val;
    TreeNode left;
    TreeNode right;

    TreeNode(int x) {
      val = x;
    }

    @Override
    public String toString() {
      return "{val=" + val + ", l=" + left + ", r=" + right + '}';
    }
  }
}
