package problems.leet100.challenges.c2020_05.w3;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/536/week-3-may-15th-may-21st/3331/
 * <p>Given a singly linked list, group all odd nodes together followed by the even nodes.
 * Please note here we are talking about the node number and not the value in the nodes.
 * You should try to do it in place. The program should run in O(1) space complexity and O(nodes) time complexity.</p>
 * <p>Note:
 * The relative order inside both the even and odd groups should remain as it was in the input.
 * The first node is considered odd, the second node even and so on ...</p>
 */
public class OddEvenLinkedListSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      final ListNode head = ListNode.of(1, 2, 3, 4, 5);
      System.out.println(oddEvenList(head));
    }
  }

  private static ListNode oddEvenList(ListNode head) {
    final ListNode result = new ListNode();

    // collect odd nodes
    ListNode j = result;
    for (ListNode i = head; i != null; i = i.next.next) {
      j.next = new ListNode(i.val);
      j = j.next;
      if (i.next == null) {
        break;
      }
    }

    // collect even nodes
    for (ListNode i = (head != null ? head.next : null); i != null; i = i.next.next) {
      j.next = new ListNode(i.val);
      j = j.next;
      if (i.next == null) {
        break;
      }
    }

    return result.next;
  }

  private static final class ListNode {
    int val;
    ListNode next;
    ListNode() {}
    ListNode(int val) { this.val = val; }
    ListNode(int val, ListNode next) { this.val = val; this.next = next; }

    static ListNode of(int... values) {
      ListNode result = new ListNode();
      ListNode it = result;
      for (final int v : values) {
        it.next = new ListNode(v);
        it = it.next;
      }
      return result.next;
    }

    @Override public String toString() {
      return val + "->" + next;
    }
  }
}
