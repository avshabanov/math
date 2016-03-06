import support.SingleLinkedListSupport;

/**
 * Prints all the permutations of a given linked list, excluding original list's representation.
 *
 * Sample run (up to list=[1, 2, 3, 4]):
 * <pre>
 * Combinations for list=[a]:
 *
 * Total: 0
 * ---
 * Combinations for list=[a, b]:
 * ba
 * Total: 1
 * ---
 * Combinations for list=[a, b, c]:
 * acb bac bca cba cab
 * Total: 5
 * ---
 * Combinations for list=[a, b, c, d]:
 * abdc acbd acdb adcb adbc bacd badc bcad bcda bdca
 * bdac cbad cbda cabd cadb cdab cdba dbca dbac dcba
 * dcab dacb dabc
 * Total: 23
 * ---
 * Combinations for list=[a, b, c, d, e]:
 * abced abdce abdec abedc abecd acbde acbed acdbe acdeb acedb acebd adcbe adceb adbce adbec adebc adecb aecdb aecbd aedcb
 * aedbc aebdc aebcd bacde baced badce badec baedc baecd bcade bcaed bcdae bcdea bceda bcead bdcae bdcea bdace bdaec bdeac
 * bdeca becda becad bedca bedac beadc beacd cbade cbaed cbdae cbdea cbeda cbead cabde cabed cadbe cadeb caedb caebd cdabe
 * cdaeb cdbae cdbea cdeba cdeab ceadb ceabd cedab cedba cebda cebad dbcae dbcea dbace dbaec dbeac dbeca dcbae dcbea dcabe
 * dcaeb dceab dceba dacbe daceb dabce dabec daebc daecb decab decba deacb deabc debac debca ebcda ebcad ebdca ebdac ebadc
 * ebacd ecbda ecbad ecdba ecdab ecadb ecabd edcba edcab edbca edbac edabc edacb eacdb eacbd eadcb eadbc eabdc eabcd
 * Total: 119
 * ---
 * ... (omitted) ...
 * </pre>
 *
 * @author Alexander Shabanov
 */
public class ListPermutationSample extends SingleLinkedListSupport {

  public static void main(String[] args) {
    demo(fromArray(new Character[] { 'a' }));
    demo(fromArray(new Character[] { 'a', 'b' }));
    demo(fromArray(new Character[] { 'a', 'b', 'c' }));
    demo(fromArray(new Character[] { 'a', 'b', 'c', 'd' }));
    demo(fromArray(new Character[] { 'a', 'b', 'c', 'd', 'e' }));
    demo(fromArray(new Character[] { 'a', 'b', 'c', 'd', 'e', 'f' }));
    demo(fromArray(new Character[] { 'a', 'b', 'c', 'd', 'e', 'f', 'g' }));
  }

  public static void demo(Node<Character> list) {
    final int expectedPermutationCount = factorial(getLength(list)) - 1;
    System.out.println("Combinations for list=" + list + ":");
    final SimplePrintListOutput<Character> output = new SimplePrintListOutput<>(getMaxRows(expectedPermutationCount));
    PermutationFinder<Character> permutationFinder = new PermutationFinder<>(list, output);
    if (list != null) {
      permutationFinder.gen(list, list.getNext());
    }

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

    public void gen(Node<T> prev, Node<T> cur) {
      if (cur == null) {
        return;
      }

      gen(cur, cur.getNext());
      swapRecursive(prev, cur);
    }

    private void swapRecursive(Node<T> prev, Node<T> cur) {
      for (Node<T> it = cur; it != null; it = it.getNext()) {
        swapValues(it, prev);
        output.print(root);

        gen(cur, cur.getNext());

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
    void print(Node<T> root);
  }

  private static abstract class AbstractPrintListOutput<T> implements ListOutput<T> {

    protected final String asString(final Node<T> root) {
      final StringBuilder builder = new StringBuilder();

      for (Node<T> it = root; it != null; it = it.getNext()) {
        builder.append(it.getValue());
      }

      return builder.toString();
    }
  }

  private static final class SimplePrintListOutput<T> extends AbstractPrintListOutput<T> {
    private final StringBuilder outputBuilder;
    private final int maxRows;
    private int curIndex = 0;

    public SimplePrintListOutput(int maxRows) {
      this.maxRows = maxRows;
      this.outputBuilder = new StringBuilder();
    }

    @Override
    public void print(Node < T > root){
      outputBuilder.append(asString(root));

      ++curIndex;
      if (curIndex % maxRows == 0) {
        outputBuilder.append('\n');
      } else {
        outputBuilder.append(' ');
      }
    }
  }
}
