import support.SingleLinkedListSupport;

import java.util.*;


/**
 * Prints all the permutations of a given linked list, excluding original list's representation.
 *
 * Sample run (up to list=[1, 2, 3, 4]):
 * <pre>
 * Combinations for list=[1]:
 *
 * Total: 0
 * ---
 * Combinations for list=[1, 2]:
 * 21
 * Total: 1
 * ---
 * Combinations for list=[1, 2, 3]:
 * 132 213 231 321 312
 * Total: 5
 * ---
 * Combinations for list=[1, 2, 3, 4]:
 * 1243 1324 1342 1432 1423 2134 2143 2314 2341 2431
 * 2413 3214 3241 3124 3142 3412 3421 4231 4213 4321
 * 4312 4132 4123
 * Total: 23
 * ---
 * Combinations for list=[1, 2, 3, 4, 5]:
 * 12354 12435 12453 12543 12534 13245 13254 13425 13452 13542
 * 13524 14325 14352 14235 14253 14523 14532 15342 15324 15432
 * 15423 15243 15234 21345 21354 21435 21453 21543 21534 23145
 * 23154 23415 23451 23541 23514 24315 24351 24135 24153 24513
 * 24531 25341 25314 25431 25413 25143 25134 32145 32154 32415
 * 32451 32541 32514 31245 31254 31425 31452 31542 31524 34125
 * 34152 34215 34251 34521 34512 35142 35124 35412 35421 35241
 * 35214 42315 42351 42135 42153 42513 42531 43215 43251 43125
 * 43152 43512 43521 41325 41352 41235 41253 41523 41532 45312
 * 45321 45132 45123 45213 45231 52341 52314 52431 52413 52143
 * 52134 53241 53214 53421 53412 53142 53124 54321 54312 54231
 * 54213 54123 54132 51342 51324 51432 51423 51243 51234
 * Total: 119
 * ---
 * ... (omitted) ...
 * </pre>
 *
 * @author Alexander Shabanov
 */
public class ListPermutationSample extends SingleLinkedListSupport {
  private static boolean PRINT_INDENT = Boolean.parseBoolean(System.getProperty("ListPermutationSample.printIndent"));

  public static void main(String[] args) {
    demo(fromArray(new Integer[] { 1 }));
    demo(fromArray(new Integer[] { 1, 2 }));
    demo(fromArray(new Integer[] { 1, 2, 3 }));
    demo(fromArray(new Integer[] { 1, 2, 3, 4 }));
    demo(fromArray(new Integer[] { 1, 2, 3, 4, 5 }));
    demo(fromArray(new Integer[] { 1, 2, 3, 4, 5, 6 }));
    demo(fromArray(new Integer[] { 1, 2, 3, 4, 5, 6, 7 }));
  }

  public static void demo(Node<Integer> list) {
    final int expectedPermutationCount = factorial(getLength(list)) - 1;
    System.out.println("Combinations for list=" + list + ":");
    final SimplePrintListOutput<Integer> output = new SimplePrintListOutput<>(PRINT_INDENT,
        getMaxRows(expectedPermutationCount));
    PermutationFinder<Integer> permutationFinder = new PermutationFinder<>(list, output);
    permutationFinder.gen(list, list.getNext(), 0);

    if (expectedPermutationCount != output.curIndex) {
      throw new AssertionError("ERROR: unexpected permutation count for given list, actual=" +
          expectedPermutationCount + ", actual=" + output.curIndex);
    }

    System.out.println(output.outputBuilder.toString() + "\nTotal: " + expectedPermutationCount + "\n---");
  }

  private static int getMaxRows(int expectedPermutationCount) {
    if (expectedPermutationCount > 1000) {
      return 40;
    } else if (expectedPermutationCount > 100) {
      return 20;
    }
    return 10;
  }

  private static final class PermutationFinder<T> {
    private final Node<T> root;
    private final ListOutput<T> output;

    public PermutationFinder(Node<T> root, ListOutput<T> output) {
      this.root = root;
      this.output = output;
    }

    public void gen(Node<T> prev, Node<T> cur, int level) {
      if (cur == null) {
        return;
      }

      gen(cur, cur.getNext(), level + 1);
      swapRecursive(prev, cur, level);
    }

    private void swapRecursive(Node<T> prev, Node<T> cur, int level) {
      for (Node<T> it = cur; it != null; it = it.getNext()) {
        swapValues(it, prev);
        output.print(root, level);

        gen(cur, cur.getNext(), level + 1);

        swapValues(it, prev); // restore changed value
      }
    }
  }

  private static int factorial(int n) {
    int result = 1;
    for (int i = n; i > 1; --i) {
      result *= i;
    }
    return result;
  }

  private static <T> void swapValues(Node<T> left, Node<T> right) {
    final T leftValue = left.getValue();
    left.setValue(right.getValue());
    right.setValue(leftValue);
  }

  private interface ListOutput<T> {
    void print(Node<T> root, int level);
  }

  private static abstract class AbstractPrintListOutput<T> implements ListOutput<T> {

    protected final String asString(final Node<T> root, final int level) {
      final StringBuilder builder = new StringBuilder();

      if (isPrintIndent()) {
        for (int i = 0; i < level; ++i) {
          builder.append(' ');
        }
      }

      for (Node<T> it = root; it != null; it = it.getNext()) {
        builder.append(it.getValue());
      }

      return builder.toString();
    }

    protected abstract boolean isPrintIndent();
  }

  private static final class SimplePrintListOutput<T> extends AbstractPrintListOutput<T> {
    private final StringBuilder outputBuilder;
    private final boolean printIndent;
    private final int maxRows;
    private int curIndex = 0;

    public SimplePrintListOutput(boolean printIndent, int maxRows) {
      this.printIndent = printIndent;
      this.maxRows = maxRows;
      this.outputBuilder = new StringBuilder();
    }

    @Override
    public void print(Node < T > root,int level){
      outputBuilder.append(asString(root, level));

      ++curIndex;
      if (curIndex % maxRows == 0) {
        outputBuilder.append('\n');
      } else {
        outputBuilder.append(' ');
      }
    }

    @Override
    protected boolean isPrintIndent() {
      return printIndent;
    }
  }
}
