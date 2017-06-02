import support.SimpleTreeSupport;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.stream.IntStream;

/**
 * Advanced console tree printer.
 * Sample run:
 * <pre>
 * <- 5 ->
 * 3     7
 *
 *    <---- 5 ---->
 * <- 3 ->     <- 7 ->
 * 2     4     6     8
 *
 *          <----- 14 --------------------->
 *      <- 12 ->                        <- 20 ------------->
 *  <- 11      13       <------------- 19               <- 24 ----------------->
 * 10                  15 ->                        <- 23                   <- 29
 *                         16 ->                <- 22               <----- 28
 *                             17 ->           21               <- 26 ->
 *                                 18                          25      27
 *
 *                                                                                                              <- 68 ------------------------->
 *                          <--------------------------------------------------------------------------------- 67                           <- 75 ----->
 *  <--------------------- 46 ----------------------------------------->                                                    <------------- 74       <- 77 ----->
 * 40 ----->                                                <--------- 57 --------->                                    <- 70 ----->               76       <- 79
 *      <- 42 ----->                <--------------------- 54 ----->        <----- 60 --------->                       69       <- 72 ->                   78
 *     41       <- 44 ->        <- 48 ----->                    <- 56      58 ->            <- 63 ->                           71      73
 *             43      45      47       <- 50 --------->       55              59       <- 62      64 ----->
 *                                     49           <- 53                              61               <- 66
 *                                              <- 52                                                  65
 *                                             51
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class TreeSuperPrinter extends SimpleTreeSupport {
  private static final char LEFT_ARROW_CHAR = '<';
  private static final char RIGHT_ARROW_CHAR = '>';
  private static final char ARROR_LINE_CHAR = '-';
  private static final int GAP = 1;

  public static void main(String[] args) {
    demo(treeFromArray(5, 3, 7));
    demo(treeFromArray(5, 3, 7, 2, 4, 6, 8));
    demo(randomTree(IntStream.range(10, 30).boxed(), new Random(493715283476345L)));
    demo(randomTree(IntStream.range(40, 80).boxed(), new Random(65342319876435235L)));
  }

  public static void demo(Node tree) {
    printTree(System.out, tree);
    System.out.print('\n');
  }

  public static void printTree(PrintStream out, INode<?, ?> tree) {
    final PrintTreeCreator.PrintNode printTree = PrintTreeCreator.toPrintTree(tree, 0);

    // print slice-by-slice
    final List<PrintTreeCreator.PrintNode> nodes = new ArrayList<>();
    if (printTree != null) {
      nodes.add(printTree);
    }

    final StringBuilder line = new StringBuilder();
    final List<PrintTreeCreator.PrintNode> childNodes = new ArrayList<>();

    while (!nodes.isEmpty()) {
      line.setLength(0);
      childNodes.clear();

      for (final PrintTreeCreator.PrintNode n : nodes) {
        // arrow to left child
        if (n.getLeft() != null) {
          appendChars(line, n.getLeft().leftOffset, ' ');
          final int arrowPos = n.getLeft().leftOffset + n.getLeft().getWrappedValueStringSize();
          appendChars(line, arrowPos - 1, ' ');
          line.append(LEFT_ARROW_CHAR);
          appendChars(line, n.leftOffset - GAP, ARROR_LINE_CHAR);

          childNodes.add(n.getLeft());
        }

        // current value
        appendChars(line, n.leftOffset, ' ');
        line.append(n.getWrappedValueAsString());

        // arrow to right child
        if (n.getRight() != null) {
          appendChars(line, line.length() + GAP, ' ');
          final int arrowPos = n.getRight().leftOffset;
          appendChars(line, arrowPos, ARROR_LINE_CHAR);
          line.append(RIGHT_ARROW_CHAR);

          childNodes.add(n.getRight());
        }
      } // for n : nodes

      // replace nodes with their childs
      nodes.clear();
      nodes.addAll(childNodes);
      out.append(line.toString()).append('\n');
    }
  }

  private static void appendChars(StringBuilder line, int pos, char ch) {
    while (line.length() < pos) {
      line.append(ch);
    }
  }

  private static final class PrintTreeCreator {


    private static PrintNode toPrintTree(INode<?, ?> tree, int offset) {
      if (tree == null) {
        return null;
      }

      final PrintNode result = new PrintNode(tree);

      // calculate size for left subtree
      final PrintNode left = toPrintTree(tree.getLeft(), offset);
      result.setLeft(left);
      result.leftOffset = (left != null ? left.rightOffset + GAP : offset);

      // calculate size for right subtree, take into an account current value size
      final int rightChildOffset = result.leftOffset + result.getWrappedValueStringSize() + GAP;
      final PrintNode right = toPrintTree(tree.getRight(), rightChildOffset + 1);
      result.setRight(right);
      result.rightOffset = (right != null ? right.rightOffset : rightChildOffset);

      return result;
    }

    private static final class PrintNode extends AbstractNode<PrintNode, INode<?, ?>> {
      private int leftOffset;
      private int rightOffset;

      protected PrintNode(INode<?, ?> value) {
        super(value);
      }

      @Override
      protected void onSetChild(PrintNode child) {}

      @Override
      public PrintNode getSelf() { return this; }

      public String getWrappedValueAsString() {
        return String.valueOf(getValue().getValue());
      }

      public int getWrappedValueStringSize() {
        return getWrappedValueAsString().length();
      }
    }

  } // class PrintTreeCreator
}
