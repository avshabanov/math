package problems.leet100.recoverTreeFromPreorderTraversal;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

/**
 * 1028. Recover a Tree From Preorder Traversal
 * https://leetcode.com/problems/recover-a-tree-from-preorder-traversal/
 *
 * <p>
 * We run a preorder depth first search on the root of a binary tree.
 *
 * At each node in this traversal, we output D dashes (where D is the depth of this node), then we output the value of this node.  (If the depth of a node is D, the depth of its immediate child is D+1.  The depth of the root node is 0.)
 *
 * If a node has only one child, that child is guaranteed to be the left child.
 *
 * Given the output S of this traversal, recover the tree and return its root.
 * </p>
 */
public class RecoverTreeFromPreorderTraversalSolution {

  public static void main(String[] args) {
    demo("1-2--3--4-5--6--7");
    demo("1-401--349---90--88");
  }

  private static void demo(String input) {
    final TreeNode root = recoverFromPreorder(input);
    System.out.println("From input=" + input + " tree=");
    System.out.println(root);
    System.out.println("---");
  }

  private static TreeNode recoverFromPreorder(String s) {
    final List<TraverseResult> traverseResults = TraverseResult.parse(s);
    if (traverseResults.isEmpty()) {
      return null;
    }
    final TreeNode treeNode = new TreeNode(-1);
    recover(treeNode, traverseResults, 0, traverseResults.size(), 0);
    return treeNode.left;
  }

  private static void recover(TreeNode root, List<TraverseResult> s, int start, int end, int depth) {
    int leftIndex = -1;
    int rightIndex = -1;

    for (int i = start; i < end; ++i) {
      final TraverseResult t = s.get(i);
      if (t.depth == depth) {
        if (leftIndex < 0) {
          leftIndex = i;
        } else {
          rightIndex = i;
          break; // skips error checking (e.g. when element w/ triplicate depth occurs on the list)
        }
      }
    }

    // find left and right subtrees in their own partitions
    if (leftIndex >= 0) {
      root.left = new TreeNode(s.get(leftIndex).value);
      recover(root.left, s, leftIndex + 1, rightIndex < 0 ? end : rightIndex, depth + 1);
    }

    if (rightIndex >= 0) {
      assert leftIndex >= start;
      root.right = new TreeNode(s.get(rightIndex).value);
      recover(root.right, s, rightIndex + 1, end, depth + 1);
    }
  }

  private static final class TraverseResult {
    final int depth;
    final int value;

    TraverseResult(int depth, int value) {
      this.depth = depth;
      this.value = value;
    }

    @Override
    public String toString() {
      final int[] dashes = IntStream.range(0, depth).map(i -> '-').toArray();
      return new String(dashes, 0, dashes.length) + value;
    }

    static List<TraverseResult> parse(String s) {
      final List<TraverseResult> results = new ArrayList<>(s.length() / 2 + 1);
      int depth = 0;
      for (int i = 0; i < s.length();) {
        char ch = s.charAt(i);
        if (ch == '-') {
          ++depth;
          ++i;
          continue;
        }

        // otherwise - expect number
        int j = i + 1;
        for (; j < s.length(); ++j) {
          if (s.charAt(j) == '-') {
            break;
          }
        }
        final int number = Integer.parseInt(s.substring(i, j));
        results.add(new TraverseResult(depth, number));
        depth = 0;
        i = j;
      }
      return results;
    }
  }

  private static class TreeNode {
    int val;
    TreeNode left;
    TreeNode right;
    TreeNode(int x) { val = x; }

    @Override
    public String toString() {
      final StringBuilder sb = new StringBuilder(100);
      print(sb, this, 0);
      return sb.toString();
    }

    private static void print(StringBuilder sb, TreeNode node, int depth) {
      if (node == null) {
        return;
      }

      print(sb, node.left, depth + 1);
      IntStream.range(0, depth).forEach(i -> sb.append(' '));
      sb.append(node.val);
      sb.append('\n');
      print(sb, node.right, depth + 1);
    }
  }
}
