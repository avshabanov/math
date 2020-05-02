package problems.leet100.challenges.c2020_04.w4;

import java.util.HashMap;
import java.util.Map;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/531/week-4/3313/
 * <p>You have a queue of integers, you need to retrieve the first unique integer in the queue.
 *
 * Implement the FirstUnique class:
 *
 * FirstUnique(int[] nums) Initializes the object with the numbers in the queue.
 * int showFirstUnique() returns the value of the first unique integer of the queue, and returns -1 if there is no such integer.
 * void add(int value) insert value to the queue.</p>
 */
public class FirstUniqueNumberSolution {

  public static final class Demo1 {

    public static void main(String[] args) {
      FirstUnique firstUnique = new FirstUnique(new int[] {2,3,5});
      checkFirstUnique(firstUnique, "[1]", 2);
      firstUnique.add(5);            // the queue is now [2,3,5,5]
      checkFirstUnique(firstUnique, "[2]", 2);
      firstUnique.add(2);            // the queue is now [2,3,5,5,2]
      checkFirstUnique(firstUnique, "[3]", 3);
      firstUnique.add(3);            // the queue is now [2,3,5,5,2,3]
      checkFirstUnique(firstUnique, "[4]", -1);
    }

    private static void checkFirstUnique(FirstUnique firstUnique, String when, int expected) {
      final int actual = firstUnique.showFirstUnique();
      if (actual != expected) {
        throw new AssertionError(when + ": expected=" + expected + ", actual=" + actual);
      }
    }
  }

  private static final class FirstUnique {

    private final Node uniqueNumberList;
    private final Map<Integer, Node> nodes = new HashMap<>();

    public FirstUnique(int[] nums) {
      this.uniqueNumberList = new Node(Integer.MIN_VALUE);
      this.uniqueNumberList.next = this.uniqueNumberList;
      this.uniqueNumberList.prev = this.uniqueNumberList;

      for (final Integer num : nums) {
        add(num);
      }
    }

    public int showFirstUnique() {
      if (this.uniqueNumberList.next != this.uniqueNumberList) {
        return this.uniqueNumberList.next.value;
      }
      return -1;
    }

    public void add(int value) {
      final Integer num = value; // box value
      Node n = nodes.get(num);
      if (n == null) {
        // this is a unique node, append it to the very end of the list
        n = new Node(num);
        this.uniqueNumberList.prev.next = n;
        n.prev = this.uniqueNumberList.prev;
        n.next = this.uniqueNumberList;
        this.uniqueNumberList.prev = n;
        nodes.put(num, n);
      } else if (n != this.uniqueNumberList) {
        // this is a non-sentinel node, it is no longer unique and hence must be excluded from the list
        // and appropriately adjusted in the map
        n.prev.next = n.next;
        n.next.prev = n.prev;
        nodes.put(num, this.uniqueNumberList);
      }
    }

    private static final class Node {
      final int value;
      Node next;
      Node prev;

      public Node(int value) {
        this.value = value;
      }

      @Override
      public String toString() {
        if (value == Integer.MIN_VALUE) {
          return "(x)";
        }
        return "(" + value + ")-->" + next.toString();
      }
    }
  }
}
