package problems.leet100.challenges.c2020_05.w1;

/**
 * https://leetcode.com/explore/featured/card/may-leetcoding-challenge/534/week-1-may-1st-may-7th/3322/
 * <p>
 * In a binary tree, the root node is at depth 0, and children of each depth k node are at depth k+1.
 * Two nodes of a binary tree are cousins if they have the same depth, but have different parents.
 * We are given the root of a binary tree with unique values, and the values x and y of two different nodes in the tree.
 * Return true if and only if the nodes corresponding to the values x and y are cousins.
 * </p><p>
 * Note:
 * The number of nodes in the tree will be between 2 and 100.
 * Each node has a unique integer value from 1 to 100.
 * </p>
 */
public class CousinsInBinaryTreeSolution {


  boolean isCousins(TreeNode root, int x, int y) {
    final CousinsFinder finder = new CousinsFinder();
    finder.findDepth(1, root, -1);
    final int xDepth = finder.depths[x];
    if (xDepth > 0) {
      return xDepth == finder.depths[y] && finder.parents[x] != finder.parents[y];
    }
    return false;
  }

  private static final class CousinsFinder {
    private static final int MAX_VALUE = 100;
    private final int[] depths = new int[MAX_VALUE + 1];
    private final int[] parents = new int[MAX_VALUE + 1];

    private void findDepth(int depth, TreeNode node, int parentVal) {
      if (node == null) {
        return;
      }

      depths[node.val] = depth;
      parents[node.val] = parentVal;
      final int newDepth = depth + 1;
      findDepth(newDepth, node.left, node.val);
      findDepth(newDepth, node.right, node.val);
    }
  }

  private static final class TreeNode {
    int val;
    TreeNode left;
    TreeNode right;
    TreeNode(int x) { val = x; }

    @Override public String toString() { return "T(" + val + ')'; }
  }
}
