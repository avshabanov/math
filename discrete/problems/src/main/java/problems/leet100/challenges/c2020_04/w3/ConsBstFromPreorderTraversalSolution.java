package problems.leet100.challenges.c2020_04.w3;

/**
 * https://leetcode.com/explore/challenge/card/30-day-leetcoding-challenge/530/week-3/3305/
 * <p>Return the root node of a binary search tree that matches the given preorder traversal.
 *
 * (Recall that a binary search tree is a binary tree where for every node, any descendant of node.left has a
 * value < node.val, and any descendant of node.right has a value > node.val.
 * Also recall that a preorder traversal displays the value of the node first, then traverses node.left,
 * then traverses node.right.)</p>
 */
public final class ConsBstFromPreorderTraversalSolution {

  public static void main(String[] args) {
    final TreeNode n = bstFromPreorder(new int[] {8,5,1,7,10,12});
    System.out.printf("n.val=%d\n", n.val);
  }

  private static final class TreeNode {
    int val;
    TreeNode left;
    TreeNode right;

    TreeNode(int x) {
      val = x;
    }
  }

  private static TreeNode bstFromPreorder(int[] preorder) {
    return bstPart(preorder, 0, preorder.length);
  }

  private static TreeNode bstPart(int[] preorder, int startIndex, int lastIndex) {
    if (startIndex >= lastIndex) {
      return null;
    }

    final TreeNode root = new TreeNode(preorder[startIndex]);
    int rightIndex = lastIndex;
    for (int i = startIndex + 1; i < lastIndex; ++i) {
      if (preorder[i] > root.val) {
        rightIndex = i;
        break;
      }
    }
    root.left = bstPart(preorder, startIndex + 1, rightIndex);
    root.right = bstPart(preorder, rightIndex, lastIndex);
    return root;
  }
}
