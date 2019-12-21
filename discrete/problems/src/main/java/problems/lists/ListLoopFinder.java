package problems.lists;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

/**
 * A solution for a problem to find a node, that starts a loop in the linked list.
 */
public final class ListLoopFinder {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println(Node.toPrettyString(createListWithLoop(3, 5), 10));
      System.out.println(Node.toPrettyString(createListWithLoop(0, 3), 7));
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      demo(createListWithLoop(3, 7), 15, ListLoopFinder::getLoopStarter);
      demo(createListWithLoop(5, 7), 15, ListLoopFinder::getLoopStarter);

      demo(createListWithLoop(0, 9), 11, ListLoopFinder::getLoopStarter);
      demo(createListWithLoop(1, 8), 11, ListLoopFinder::getLoopStarter);
      demo(createListWithLoop(2, 7), 11, ListLoopFinder::getLoopStarter);
      demo(createListWithLoop(3, 6), 11, ListLoopFinder::getLoopStarter);
      demo(createListWithLoop(4, 5), 11, ListLoopFinder::getLoopStarter);
      demo(createListWithLoop(5, 4), 11, ListLoopFinder::getLoopStarter);
      demo(createListWithLoop(6, 3), 11, ListLoopFinder::getLoopStarter);
      demo(createListWithLoop(7, 2), 11, ListLoopFinder::getLoopStarter);
      demo(createListWithLoop(8, 1), 11, ListLoopFinder::getLoopStarter);
    }
  }

  public static final class Demo3 {
    public static void main(String[] args) {
      demo(createListWithLoop(1, 7), 10, ListLoopFinder::getLoopStarterUnopt);
      demo(createListWithLoop(2, 6), 10, ListLoopFinder::getLoopStarterUnopt);
      demo(createListWithLoop(3, 5), 11, ListLoopFinder::getLoopStarterUnopt);
    }
  }

  private static void demo(Node list, int printLimit, Function<Node, Node> getLoopFunc) {
    final Node loopStarter = getLoopFunc.apply(list);
    System.out.printf("A list %s contains loop: %s\n",
        Node.toPrettyString(list, printLimit),
        loopStarter != null ? loopStarter.value : "<none>");
  }

  private static Node getLoopStarterUnopt(Node list) {
    final Set<Node> nodes = new HashSet<>();
    for (Node n = list; n != null; n = n.next) {
      if (!nodes.add(n)) {
        return n;
      }
    }
    return null;
  }

  private static Node getLoopStarter(Node list) {
    // 1st phase: find a point within the loop
    Node innerLoopNode = null;
    boolean move = false;
    for (Node n1 = list, n2 = list.next; n2 != null; n2 = n2.next) {
      if (move) {
        n1 = n1.next;
      }
      move = !move;
      if (n1 == n2) {
        innerLoopNode = n1;
        break;
      }
    }

    if (innerLoopNode == null) {
      return null; // this list has no loop
    }

    // 2nd phase: move one node by one until loop is found
    for (Node n = list;; n = n.next) {
      Node u = innerLoopNode;
      do {
        if (n == u) {
          return n;
        }
        u = u.next;
      } while (u != innerLoopNode);
    }
  }

  private static final class Node {
    final int value;
    Node next;

    Node(int value) {
      this.value = value;
    }

    static String toPrettyString(Node n, int limit) {
      final StringBuilder sb = new StringBuilder(limit * 5 + 10);
      for (int i = 0; i < limit && n != null; ++i, n = n.next) {
        if (i > 0) {
          sb.append("->");
        }
        sb.append(n.value);
      }
      sb.append("->...");
      return sb.toString();
    }
  }

  private static Node createListWithLoop(int prefixSize, int loopSize) {
    Node result = null;
    Node cursor = null;
    int val = 0;
    for (int i = 0; i < prefixSize; ++i) {
      final Node n = new Node(val++);
      if (cursor == null) {
        cursor = n;
        result = n;
      } else {
        cursor.next = n;
        cursor = n;
      }
    }

    Node loopStart = null;
    for (int i = 0; i < loopSize; ++i) {
      final Node n = new Node(val++);
      if (cursor == null) {
        cursor = n;
        result = n;
      } else {
        cursor.next = n;
        cursor = n;
      }

      if (loopStart == null) {
        loopStart = n;
      }
    }

    if (loopStart != null) {
      // introduce a loop
      cursor.next = loopStart;
    }

    return result;
  }
}
