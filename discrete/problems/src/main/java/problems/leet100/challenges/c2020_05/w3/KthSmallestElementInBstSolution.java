package problems.leet100.challenges.c2020_05.w3;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/536/week-3-may-15th-may-21st/3335/
 * <p>Given a binary search tree, write a function kthSmallest to find the kth smallest element in it.
 *
 * Note:
 * You may assume k is always valid, 1 ≤ k ≤ BST's total elements.</p>
 */
public class KthSmallestElementInBstSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      final TreeNode n = new TreeNode(3);
      n.left = new TreeNode(1);
      n.left.right = new TreeNode(2);
      n.right = new TreeNode(4);

      System.out.println("k(0) = " + kthSmallest(n, 1));
      System.out.println("k(1) = " + kthSmallest(n, 2));
    }
  }

  private static int kthSmallest(TreeNode root, int k) {
    final ElementFinder finder = new ElementFinder(k);
    if (finder.find(root, 0) >= 0) {
      throw new IllegalStateException("element has not been found");
    }
    return finder.result.val;
  }

  private static final class ElementFinder {
    TreeNode result;
    final int k;

    public ElementFinder(int k) {
      this.k = k;
    }

    int find(TreeNode node, int offset) {
      if (node == null) {
        return offset;
      }
      final int leftCount = find(node.left, offset);
      if (leftCount < 0) {
        return -1; // shortcut: found solution
      }

      if (leftCount == k - 1) {
        result = node;
        return -1; // shortcut: found solution
      }

      return find(node.right, leftCount + 1);
    }
  }

  public static final class TreeNode {
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
}
