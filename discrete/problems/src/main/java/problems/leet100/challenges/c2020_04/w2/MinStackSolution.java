package problems.leet100.challenges.c2020_04.w2;

import java.util.Arrays;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/529/week-2/3292/
 * <p>Design a stack that supports push, pop, top, and retrieving the minimum element in constant time.
 *
 * push(x) -- Push element x onto stack.
 * pop() -- Removes the element on top of the stack.
 * top() -- Get the top element.
 * getMin() -- Retrieve the minimum element in the stack.</p>
 */
public class MinStackSolution {

  public static void main(String[] args) {
    MinStack minStack = new MinStack();
    minStack.push(-2);
    minStack.push(0);
    minStack.push(-3);
    System.out.println("1: getMin=" + minStack.getMin());
    minStack.pop();
    System.out.println("2: top=" + minStack.top());
    System.out.println("3: getMin=" + minStack.getMin());
  }

  private static class MinStack {

    private static final class Node {
      final int minValue;
      final int value;

      public Node(int minValue, int value) {
        this.minValue = minValue;
        this.value = value;
      }
    }

    private Node[] nodes = new Node[4];
    private int size = 0;

    public MinStack() {
    }

    public void push(int x) {
      if (size >= nodes.length) {
        nodes = Arrays.copyOf(nodes, nodes.length * 2);
      }
      final Node node = new Node(Math.min(x, size > 0 ? nodes[size - 1].minValue : x), x);
      nodes[size] = node;
      ++size;
    }

    public void pop() {
      if (size == 0) {
        throw new IllegalStateException("empty stack");
      }
      --size;
    }

    public int top() {
      if (size == 0) {
        throw new IllegalStateException("empty stack");
      }
      return nodes[size - 1].value;
    }

    public int getMin() {
      if (size == 0) {
        throw new IllegalStateException("empty stack");
      }
      return nodes[size - 1].minValue;
    }
  }
}
