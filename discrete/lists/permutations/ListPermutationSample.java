import support.SingleLinkedListSupport;


/**
 * Prints all the permutations of a given linked list, excluding original list's representation.
 *
 * Sample run (up to list=[1, 2, 3, 4]):
 * <pre>
 * Combinations for list=[1]:
 * ---
 * Combinations for list=[1, 2]:
 * 21
 * ---
 * Combinations for list=[1, 2, 3]:
 * 132
 * 213
 * 231
 * 321
 * 312
 * ---
 * Combinations for list=[1, 2, 3, 4]:
 * 1243
 * 1324
 * 1342
 * 1432
 * 1423
 * 2134
 * 2143
 * 2314
 * 2341
 * 2431
 * 2413
 * 3214
 * 3241
 * 3124
 * 3142
 * 3412
 * 3421
 * 4231
 * 4213
 * 4321
 * 4312
 * 4132
 * 4123
 * </pre>
 *
 * @author Alexander Shabanov
 */
public class ListPermutationSample extends SingleLinkedListSupport {
  private static boolean PRINT_INDENT = Boolean.parseBoolean(System.getProperty("ListPermutationSample.printIndent"));

  public static void main(String[] args) {
    demo(fromArray(new Integer[] { 1, 2, 3 }));

//    demo(fromArray(new Integer[] { 1 }));
//    demo(fromArray(new Integer[] { 1, 2 }));
//    demo(fromArray(new Integer[] { 1, 2, 3 }));
//    demo(fromArray(new Integer[] { 1, 2, 3, 4 }));
//    demo(fromArray(new Integer[] { 1, 2, 3, 4, 5 }));
  }

  public static void demo(Node<Integer> list) {
    System.out.println("Combinations for list=" + list + ":");
    gen(list, list, list.getNext(), 0);
    System.out.println("---");
  }

  private static <T> void gen(Node<T> root, Node<T> prev, Node<T> cur, int level) {
    if (cur == null) {
      return;
    }

    gen(root, cur, cur.getNext(), level + 1);
    swapRecursive(root, prev, cur, level);
  }

  private static <T> void swapRecursive(Node<T> root, Node<T> prev, Node<T> cur, int level) {
    for (Node<T> it = cur; it != null; it = it.getNext()) {
      swapValues(it, prev);
      print(root, level);

      gen(root, cur, cur.getNext(), level + 1);

      swapValues(it, prev); // restore changed value
    }
  }

  private static <T> void swapValues(Node<T> left, Node<T> right) {
    final T leftValue = left.getValue();
    left.setValue(right.getValue());
    right.setValue(leftValue);
  }

  private static <T> void print(final Node<T> root, int level) {
    final StringBuilder builder = new StringBuilder();

    if (PRINT_INDENT) {
      for (int i = 0; i < level; ++i) {
        builder.append(' ');
      }
    }

    for (Node<T> it = root; it != null; it = it.getNext()) {
      builder.append(it.getValue());
    }

    System.out.println(builder.toString());
  }
}
