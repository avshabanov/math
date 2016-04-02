import support.SimpleTreeSupport;

import java.util.Objects;

/**
 * Sample run:
 * <pre>
 *
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class TreeComparisonExample extends SimpleTreeSupport {

  public static void main(String[] args) {
    demo("null1", null, "null2", null);
    demo("null1", null, "n(1)", n(1));
    demo("n(1)", n(1), "null2", null);
    demo("n(1)", n(1), "n(1)", n(1));
    demo("n(321)", n(3, n(1), n(2)), "n(321)", n(3, n(1), n(2)));
    demo("n(321)", n(3, n(1), n(2)), "n(322)", n(3, n(2), n(2)));
    demo("n(321)", n(3, n(1), n(2)), "n(31n)", n(3, n(1), null));
  }

  public static void demo(String lhsName, Node lhs, String rhsName, Node rhs) {
    System.out.println("Tree " + lhsName + " and " + rhsName + "\tare " +
        (nodeEquals(lhs, rhs) ? "" : "not ") + "equal");
  }

  public static boolean nodeEquals(Node lhs, Node rhs) {
    if (lhs == null) {
      return rhs == null;
    }

    if (rhs == null) {
      return false;
    }

    if (!Objects.equals(lhs.getValue(), rhs.getValue())) {
      return false;
    }

    return nodeEquals(lhs.getLeft(), rhs.getLeft()) && nodeEquals(lhs.getRight(), rhs.getRight());
  }
}
