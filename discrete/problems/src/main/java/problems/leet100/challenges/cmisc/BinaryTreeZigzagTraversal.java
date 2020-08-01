package problems.leet100.challenges.cmisc;

import java.util.ArrayList;
import java.util.List;

/**
 * Binary Tree Zigzag Level Order Traversal
 * Given a binary tree, return the zigzag level order traversal of its nodes' values. (ie, from left to right,
 * then right to left for the next level and alternate between).
 */
public class BinaryTreeZigzagTraversal {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println("z(nil)=" + zigzagLevelOrder(null));
      System.out.println("z(1)=" + zigzagLevelOrder(new TreeNode(1)));
      System.out.println("z(1)=" + zigzagLevelOrder(new TreeNode(1, new TreeNode(2), new TreeNode(3))));
    }
  }

  private static final class TreeNode {
    int val;
    TreeNode left;
    TreeNode right;
    TreeNode() {}
    TreeNode(int val) { this.val = val; }
    TreeNode(int val, TreeNode left, TreeNode right) {
      this.val = val;
      this.left = left;
      this.right = right;
    }
  }

  private static List<List<Integer>> zigzagLevelOrder(TreeNode root) {
    final List<List<Integer>> result = new ArrayList<>();
    List<TreeNode> slice = new ArrayList<>();
    if (root != null) {
      slice.add(root);
    }

    for (boolean rtl = false; !slice.isEmpty(); rtl = !rtl) {
      final List<TreeNode> nextSlice = new ArrayList<>();
      final List<Integer> values = new ArrayList<>();
      for (int i = 0; i < slice.size(); ++i) {
        values.add(slice.get(rtl ? (slice.size() - i - 1) : i).val);
        final TreeNode ltrLayerNode = slice.get(i);
        if (ltrLayerNode.left != null) {
          nextSlice.add(ltrLayerNode.left);
        }
        if (ltrLayerNode.right != null) {
          nextSlice.add(ltrLayerNode.right);
        }
      }
      slice = nextSlice;
      result.add(values);
    }

    return result;
  }
}
