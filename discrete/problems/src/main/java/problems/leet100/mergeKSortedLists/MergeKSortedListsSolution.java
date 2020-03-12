package problems.leet100.mergeKSortedLists;

import java.util.Arrays;
import java.util.Map;
import java.util.TreeMap;

/**
 * 23. Merge k Sorted Lists
 * https://leetcode.com/problems/merge-k-sorted-lists/
 * <p>
 * Merge k sorted linked lists and return it as one sorted list. Analyze and describe its complexity.
 * Example:
 * Input:
 * [
 *   1->4->5,
 *   1->3->4,
 *   2->6
 * ]
 * Output: 1->1->2->3->4->4->5->6
 * </p>
 */
public class MergeKSortedListsSolution {

  public static void main(String[] args) {
    demo(new ListNode[] {
        ListNode.of(1, 2, 3)
    });

    demo(new ListNode[] {
        ListNode.of(1),
        ListNode.of(2),
        ListNode.of(3)
    });

    demo(new ListNode[] {
        ListNode.of(1, 4),
        ListNode.of(2, 5, 7, 9),
        ListNode.of(3, 6, 8)
    });
  }

  private static void demo(ListNode[] lists) {
    ListNode result = mergeKLists(lists);
    System.out.printf("Input: %s\nOutput: %s\n",
        Arrays.toString(Arrays.stream(lists).map(ListNode::toString).toArray()),
        result);
  }

  private static ListNode mergeKLists(ListNode[] lists) {
    final TreeMap<ValueKey, ListNode> valueKeys = new TreeMap<>();
    // initial import
    for (int i = 0; i < lists.length; ++i) {
      final ListNode n = lists[i];
      if (n == null) {
        continue;
      }
      valueKeys.put(new ValueKey(i, n.val), n);
    }

    ListNode head = new ListNode(-1);
    ListNode tail = head;
    while (!valueKeys.isEmpty()) {
      // pick minimal value
      final Map.Entry<ValueKey, ListNode> e = valueKeys.firstEntry(); // O(1)
      final ValueKey key = e.getKey();
      valueKeys.remove(key); // O(1)

      ListNode n = e.getValue();

      // is this the only remaining element? - if yes, then append all the remaining items and we're done
      if (valueKeys.isEmpty()) {
        for (; n != null; n = n.next) {
          tail.next = new ListNode(n.val);
          tail = tail.next;
        }
        break;
      }

      final ValueKey nextKey = valueKeys.firstKey(); // O(1)

      // pick next value, keep adding until we hit next minimum
      do {
        if (n.val > nextKey.value) {
          break; // immediately stop if next closest element is exceeding this
        }

        tail.next = new ListNode(n.val);
        tail = tail.next;
        n = n.next;
      } while (n != null);

      if (n != null) {
        // put updated value back to the list
        key.value = n.val;
        valueKeys.put(key, n); // O(k)
      }
    }

    return head.next;
  }

  private static final class ValueKey implements Comparable<ValueKey> {
    int value;
    final int listIndex;

    public ValueKey(int listIndex, int value) {
      this.listIndex = listIndex;
      this.value = value;
    }

    @Override
    public int compareTo(ValueKey o) {
      final int result = Integer.compare(value, o.value);
      return result != 0 ? result : Integer.compare(listIndex, o.listIndex);
    }
  }

  private static class ListNode {
    int val;
    ListNode next;
    ListNode(int x) { val = x; }

    static ListNode of(int... values) {
      ListNode head = new ListNode(-1);
      ListNode tail = head;

      for (int value : values) {
        tail.next = new ListNode(value);
        tail = tail.next;
      }

      return head.next;
    }

    @Override public String toString() { return "" + val + (next == null ? "" : "->" + next); }
  }
}
