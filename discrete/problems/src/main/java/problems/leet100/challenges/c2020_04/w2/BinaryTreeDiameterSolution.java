package problems.leet100.challenges.c2020_04.w2;

import java.util.stream.IntStream;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/529/week-2/3293/
 * <p>Given a binary tree, you need to compute the length of the diameter of the tree. The diameter of a binary tree is
 * the length of the longest path between any two nodes in a tree. This path may or may not pass through the root.</p>
 */
public class BinaryTreeDiameterSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      final TreeNode[] n = TreeNode.arrayOf(0, 1, 2, 3, 4, 5);
      n[1].left = n[2];
      n[1].right = n[3];
      n[2].left = n[4];
      n[2].right = n[5];

      int d = diameterOfBinaryTree(n[1]);
      System.out.println("d=" + d);
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      final TreeNode[] n = TreeNode.arrayOf(0, 1, 2);
      n[0].left = n[1];
      n[1].right = n[2];

      int d = diameterOfBinaryTree(n[0]);
      System.out.println("d=" + d);
    }
  }



  private static final class TreeNode {
    int val;
    TreeNode left;
    TreeNode right;
    TreeNode(int x) { val = x; }

    static TreeNode[] arrayOf(int... values) {
      return IntStream.of(values).mapToObj(TreeNode::new).toArray(TreeNode[]::new);
    }

    @Override
    public String toString() {
      return "T(" + val + ')';
    }
  }

  private static int diameterOfBinaryTree(TreeNode root) {
    final Solver s = new Solver();
    s.maxSubtree(root);
    return s.maxLeft + s.maxRight;
  }

  private static final class Solver {
    int maxLeft = 0;
    int maxRight = 0;

    private int maxSubtree(TreeNode root) {
      if (root == null) {
        return -1;
      }

      final int maxLeft = 1 + maxSubtree(root.left);
      final int maxRight = 1 + maxSubtree(root.right);
      final int maxDiameter = maxLeft + maxRight;
      if (maxDiameter > (this.maxLeft + this.maxRight)) {
        this.maxLeft = maxLeft;
        this.maxRight = maxRight;
      }

      return Math.max(maxLeft, maxRight);
    }
  }
}
