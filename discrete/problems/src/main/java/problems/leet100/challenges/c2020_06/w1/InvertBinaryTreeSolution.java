package problems.leet100.challenges.c2020_06.w1;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/539/week-1-june-1st-june-7th/3347/
 * <p>Invert a binary tree.</p>
 * <p>Trivia:
 * This problem was inspired by this original tweet by Max Howell:
 * Google: 90% of our engineers use the software you wrote (Homebrew), but you can’t invert a binary tree on
 * a whiteboard so f*** off.</p>
 */
public class InvertBinaryTreeSolution {

  private static TreeNode invertTree(TreeNode root) {
    if (root == null) {
      return null;
    }
    return new TreeNode(root.val, invertTree(root.right), invertTree(root.left));
  }

  private static class TreeNode {
    int val;
    TreeNode left;
    TreeNode right;

    TreeNode() {
    }

    TreeNode(int val) {
      this.val = val;
    }

    TreeNode(int val, TreeNode left, TreeNode right) {
      this.val = val;
      this.left = left;
      this.right = right;
    }
  }
}
