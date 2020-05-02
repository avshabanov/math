package problems.leet100.challenges.c2020_04.w5;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/532/week-5/3314/
 * <p>Given a non-empty binary tree, find the maximum path sum.
 *
 * For this problem, a path is defined as any sequence of nodes from some starting node to any node in the tree along
 * the parent-child connections. The path must contain at least one node and does not need to go through the root.</p>
 */
public class BinaryTreeMaximumPathSumSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      final TreeNode root = new TreeNode(-10);
      root.left = new TreeNode(9);
      root.right = new TreeNode(20);
      root.right.left = new TreeNode(15);
      root.right.right = new TreeNode(7);
      System.out.printf("Output: %d\n", Custom.maxPathSum(root));
    }
  }

  private static final class Custom {

    private static int maxPathSum(TreeNode root) {
      final Solver s = new Solver();
      s.maxPathSum(root);
      return s.maxPath;
    }

    private static final class Solver {
      int maxPath = Integer.MIN_VALUE;

      public int maxPathSum(TreeNode node) {
        if (node == null) {
          return 0;
        }

        final int leftSum = maxPathSum(node.left) + node.val;
        final int rightSum = maxPathSum(node.right) + node.val;

        // try this node alone
        maxPath = Math.max(node.val, maxPath);
        // try left subtree + this node
        maxPath = Math.max(leftSum, maxPath);
        // try right subtree + this node
        maxPath = Math.max(rightSum, maxPath);
        // try left and right connecting through current node
        maxPath = Math.max(leftSum + rightSum - node.val, maxPath);
        // return maximum path segment that can be constructed from the subtree containing this node
        return Math.max(node.val, Math.max(leftSum, rightSum));
      }
    }
  }

  private static final class Leaked {
    int maxPathSum(TreeNode root) {
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

        // pass upwards either:
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

  private static class TreeNode {
    int val;
    TreeNode left;
    TreeNode right;
    TreeNode(int x) { val = x; }
    @Override public String toString() {
      return "{val=" + val + ", l=" + left + ", r=" + right + '}';
    }
  }
}
