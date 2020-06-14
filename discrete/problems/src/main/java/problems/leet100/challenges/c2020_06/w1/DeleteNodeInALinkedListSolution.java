package problems.leet100.challenges.c2020_06.w1;

/**
 * https://leetcode.com/explore/challenge/card/june-leetcoding-challenge/539/week-1-june-1st-june-7th/3348/
 */
public class DeleteNodeInALinkedListSolution {

  private static void deleteNode(ListNode node) {
    for (;;) {
      node.val = node.next.val;
      if (node.next.next == null) {
        node.next = null;
        break;
      } else {
        node = node.next;
      }
    }
  }

  private static class ListNode {
    int val;
    ListNode next;
    ListNode(int x) { val = x; }
  }
}
