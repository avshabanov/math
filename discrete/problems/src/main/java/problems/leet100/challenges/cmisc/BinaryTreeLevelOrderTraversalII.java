package problems.leet100.challenges.cmisc;

import java.util.*;
import java.util.stream.Collectors;

/**
 * https://leetcode.com/explore/challenge/card/july-leetcoding-challenge/544/week-1-july-1st-july-7th/3378/
 * <p>Given a binary tree, return the bottom-up level order traversal of its nodes' values.
 * (ie, from left to right, level by level from leaf to root).</p>
 */
public class BinaryTreeLevelOrderTraversalII {

  public static void main(String[] args) {
    System.out.println("f(nil)=" + levelOrderBottom(null));
    System.out.println("f(1)=" + levelOrderBottom(new TreeNode(1)));
    System.out.println("f(1)=" + levelOrderBottom(new TreeNode(1, new TreeNode(2), new TreeNode(3))));
  }

  private static List<List<Integer>> levelOrderBottom(TreeNode root) {
    final List<List<Integer>> result = new ArrayList<>();
    final Deque<List<TreeNode>> nodes = new ArrayDeque<>();
    if (root != null) {
      nodes.add(Collections.singletonList(root));
    }

    // add all layers
    while (!nodes.isEmpty()) {
      final List<TreeNode> lastLayer = nodes.peekLast();
      final List<TreeNode> nextLayer = new ArrayList<>();
      for (final TreeNode n : lastLayer) {
        if (n.left != null) {
          nextLayer.add(n.left);
        }
        if (n.right != null) {
          nextLayer.add(n.right);
        }
      }
      if (nextLayer.isEmpty()) {
        break;
      }
      nodes.addLast(nextLayer);
    }

    // peel all layers
    while (!nodes.isEmpty()) {
      final List<TreeNode> last = nodes.pollLast();
      result.add(last.stream().map(n -> n.val).collect(Collectors.toList()));
    }

    return result;
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
}
