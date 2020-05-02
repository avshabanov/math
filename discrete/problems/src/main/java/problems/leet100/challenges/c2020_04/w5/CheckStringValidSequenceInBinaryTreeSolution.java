package problems.leet100.challenges.c2020_04.w5;

import java.util.Arrays;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/532/week-5/3315/
 * <p>Given a binary tree where each path going from the root to any leaf form a valid sequence,
 * check if a given string is a valid sequence in such binary tree.
 *
 * We get the given string from the concatenation of an array of integers arr and the concatenation of all values of
 * the nodes along a path results in a sequence in the given binary tree.</p>
 */
public class CheckStringValidSequenceInBinaryTreeSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      final TreeNode root = new TreeNode(0);

      root.left = new TreeNode(1);
      root.left.left = new TreeNode(0);
      root.left.left.right = new TreeNode(1);
      root.left.right = new TreeNode(1);
      root.left.right.left = new TreeNode(0);
      root.left.right.right = new TreeNode(0);

      root.right = new TreeNode(0);
      root.right.left = new TreeNode(0);

      demo(root, true, 0, 0, 0);
      demo(root, false, 0, 0, 0, 1);
      demo(root, true, 0, 1, 0, 1);
      demo(root, true, 0, 1, 1, 0);
      demo(root, false, 0, 1, 1, 1);
      demo(root, false, 0, 1, 1);
      demo(root, false, 0, 1, 0);
    }

    private static void demo(TreeNode root, boolean expected, int... arr) {
      if (expected != isValidSequence(root, arr)) {
        throw new AssertionError("Mismatch for array=" + Arrays.toString(arr));
      }
      System.out.printf("Match for %s\n", Arrays.toString(arr));
    }
  }

  private static boolean isValidSequence(TreeNode root, int[] arr) {
    if (root == null || arr == null || arr.length == 0) {
      return false;
    }
    return isValidSequence(root, arr, 0);
  }

  private static boolean isValidSequence(TreeNode node, int[] arr, int pos) {
    if (node.val != arr[pos]) {
      return false;
    }

    final int nextPos = pos + 1;
    if (nextPos == arr.length) {
      return node.left == null && node.right == null;
    }

    if (node.left != null && isValidSequence(node.left, arr, nextPos)) {
      return true;
    }

    return node.right != null && isValidSequence(node.right, arr, nextPos);
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
