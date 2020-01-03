package problems.leet100.binaryTreeMaximumPathSum;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * 124. Binary Tree Maximum Path Sum
 * https://leetcode.com/problems/binary-tree-maximum-path-sum/
 * <p>Given a non-empty binary tree, find the maximum path sum.
 * For this problem, a path is defined as any sequence of nodes from some starting node to any node in the tree
 * along the parent-child connections. The path must contain at least one node and
 * does not need to go through the root.</p>
 */
public class BinaryTreeMaximumPathSumSolution {

  public static class TreeNode {
    int val;
    TreeNode left;
    TreeNode right;

    TreeNode(int x) {
      val = x;
    }
  }

  public static void main(String[] args) {
    demo(new Integer[]{5,4,8,11,null,13,4,7,2,null,null,null,1});
    demo(new Integer[]{1,2,3});
    demo(new Integer[]{-10,9,20,null,null,15,7});
  }

  private static void demo(Integer[] treeValues) {
    TreeNode root = treeFromList(treeValues);
    int maxSum = maxPathSum(root);
    System.out.printf("For tree=%s max sum=%d\n", Arrays.toString(treeValues), maxSum);
  }

  private static TreeNode treeFromList(Integer[] treeValues) {
    List<TreeNode> layer = new ArrayList<>();
    TreeNode root = null;
    for (int i = 1, pos = 0; pos < treeValues.length; i = i * 2) {
      if (i == 1) {
        root = new TreeNode(treeValues[0]);
        layer.add(root);
        ++pos;
        continue;
      }

      final List<TreeNode> nextLayer = new ArrayList<>();
      for (int j = 0; j < i && pos < treeValues.length; ++j) {
        TreeNode node = layer.get(j / 2);
        Integer val = treeValues[pos++];
        if (val == null || node == null) {
          nextLayer.add(null);
          continue;
        }

        TreeNode child = new TreeNode(val);
        if (j % 2 == 0) {
          node.left = child;
        } else {
          node.right = child;
        }
        nextLayer.add(child);
      }
      layer = nextLayer;
    }
    return root;
  }

  private static int maxPathSum(TreeNode root) {
    final MaxPathSumFinder finder = new MaxPathSumFinder();
    finder.maxPathSum(root);
    return finder.maxFoundSum;
  }

  private static class MaxPathSumFinder {
    int maxFoundSum = Integer.MIN_VALUE;

    int maxPathSum(TreeNode root) {
      if (root == null) {
        return 0;
      }

      final int leftSum = maxPathSum(root.left);
      final int rightSum = maxPathSum(root.right);

      // pass upwards either, whichever is greater:
      //  (1) this node alone
      //  (2) this node + left subtree sum
      //  (3) this node + right subtree sum
      final int maxPathSum = Math.max(
          root.val,
          Math.max(root.val + leftSum, root.val + rightSum));

      // in order to account for complete path reachable from this node, we need to account for path sums and
      // in addition this node plus left and right subtrees
      final int maxNodeSum = Math.max(maxPathSum, root.val + leftSum + rightSum);
      this.maxFoundSum = Math.max(this.maxFoundSum, maxNodeSum);

      return maxPathSum;
    }
  }
}
