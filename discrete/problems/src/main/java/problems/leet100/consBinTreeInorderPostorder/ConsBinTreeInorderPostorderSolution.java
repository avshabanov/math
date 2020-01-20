package problems.leet100.consBinTreeInorderPostorder;

import java.util.Arrays;

/**
 * 106. Construct Binary Tree from Inorder and Postorder Traversal
 * https://leetcode.com/problems/construct-binary-tree-from-inorder-and-postorder-traversal/
 * <p>Given inorder and postorder traversal of a tree, construct the binary tree.
 *
 * Note:
 * You may assume that duplicates do not exist in the tree.</p>
 */
public class ConsBinTreeInorderPostorderSolution {
  public static void main(String[] args) {
    demo(
        new int[]{9,3,15,20,7},
        new int[]{9,15,7,20,3}
    );
  }

  private static void demo(int[] inorder, int[] postorder) {
    final TreeNode n = buildTree(inorder, postorder);
    System.out.printf(
        "For inorder=%s, postorder=%s root=%s\n",
        Arrays.toString(inorder),
        Arrays.toString(postorder),
        n == null ? "null" : n.val
    );
  }

  private static TreeNode buildTree(int[] inorder, int[] postorder) {
    return buildTree(inorder, 0, inorder.length, postorder, 0, postorder.length);
  }

  private static TreeNode buildTree(
      int[] inorder, int inoStart, int inoEnd,
      int[] postorder, int poStart, int poEnd
  ) {
    if (poStart >= poEnd) {
      return null;
    }

    final TreeNode root = new TreeNode(postorder[poEnd - 1]);
    int inoRootNodeIndex = -1;
    for (int i = inoStart; i < inoEnd; ++i) {
      if (inorder[i] == root.val) {
        inoRootNodeIndex = i;
        break;
      }
    }
    if (inoRootNodeIndex < 0) {
      throw new IllegalStateException("root node has not been found in inorder arr");
    }

    final int leftSubtreeSize = inoRootNodeIndex - inoStart;
    root.left = buildTree(
      inorder, inoStart, inoRootNodeIndex,
      postorder, poStart, poStart + leftSubtreeSize
    );
    root.right = buildTree(
        inorder, inoRootNodeIndex + 1, inoEnd,
        postorder, poStart + leftSubtreeSize, poEnd - 1
    );

    return root;
  }

  private static class TreeNode {
    int val;
    TreeNode left;
    TreeNode right;
    TreeNode(int x) { val = x; }
  }
}
