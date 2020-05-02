package problems.leet100.challenges.c2020_04.w2;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/529/week-2/3290/
 * <p>
 * Given a non-empty, singly linked list with head node head, return a middle node of linked list.
 * If there are two middle nodes, return the second middle node.
 * </p>
 */
public class MiddleOfTheLinkedListSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      ListNode n = ListNode.of(1,2,3,4,5,6);
      System.out.printf("n=%s, mid=%s\n", n, middleNode(n));
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      ListNode n = ListNode.of(1,2,3,4,5);
      System.out.printf("n=%s, mid=%s\n", n, middleNode(n));
    }
  }

  private static ListNode middleNode(ListNode head) {
    int count = 0;
    for (ListNode n = head; n != null; n = n.next) {
      ++count;
    }
    count = count / 2;

    ListNode n = head;
    for (int i = 0; i < count; ++i) {
      n = n.next;
    }
    return n;
  }


  private static class ListNode {
    int val;
    ListNode next;
    ListNode(int x) { val = x; }

    static ListNode of(int... values) {
      final ListNode head = new ListNode(values[0]);
      ListNode it = head;
      for (int i = 1; i < values.length; ++i) {
        final ListNode n = new ListNode(values[i]);
        it.next = n;
        it = n;
      }
      return head;
    }

    @Override
    public String toString() {
      return "(" + val + ')' + (next == null ? "" : ("->" + next.toString()));
    }
  }
}
