import support.SimpleTreeSupport;


/**
 * Illustration of non-recursive implementation of 'find-next' algorithm in binary tree without using recursion and
 * any other helper data structures.
 *
 * Sample output:
 *
 * <code>
 * tree=
 *     20
 *   30
 *     40
 * 50
 *     60
 *   70
 *     80
 *
 * 	value greater than=15 is 20
 * 	value greater than=25 is 30
 * 	value greater than=35 is 40
 * 	value greater than=45 is 50
 * 	value greater than=55 is 60
 * 	value greater than=65 is 70
 * 	value greater than=75 is 80
 * 	value greater than=85 is (none)
 * tree=
 * 50
 *
 * 	value greater than=40 is 50
 * 	value greater than=50 is (none)
 * 	value greater than=60 is (none)
 * </code>
 *
 * @author Alexander Shabanov
 */
public final class NonRecursiveFindNextExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo(new Integer[] {50, 30, 70, 20, 40, 60, 80}, new int[] {15, 25, 35, 45, 55, 65, 75, 85});
    demo(new Integer[] {50}, new int[] {40, 50, 60});
  }

  //
  // Private
  //

  private static void demo(Integer[] treeValues, int[] valuesGreaterThan) {
    final Node tree = treeFromArray(treeValues);
    System.out.println("tree=\n" + asString(tree));
    for (final int value : valuesGreaterThan) {
      final Node node = findNodeWithValueGreaterThan(tree, value);
      System.out.println("\tvalue greater than=" + value + " is " + (node == null ? "(none)" : node.getValue()));
    }
  }

  private static Node findNodeWithValueGreaterThan(Node node, int element) {
    Node candidate = null;
    for (;;) {
      for (;;) {
        if (node == null) {
          break;
        }

        if (element >= node.getValue()) {
          node = node.getRight(); // go to the right node until we meet a node which will be greater
        } else {
          break;
        }
      }

      if (node == null) {
        return candidate;
      } else {
        // element is strictly less than the given one - try to find something in the left subtree
        candidate = node;
        node = node.getLeft();
      }
    }
  }
}
