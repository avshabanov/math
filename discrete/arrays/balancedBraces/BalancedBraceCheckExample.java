import java.util.*;

/**
 * Sample output:
 * <pre>
 * OK: input=, balanced?=true
 * OK: input=a, balanced?=true
 * OK: input=(a), balanced?=true
 * OK: input=([{}]), balanced?=true
 * OK: input=([{]}), balanced?=false
 * OK: input=[({]}), balanced?=false
 * OK: input=(a, balanced?=false
 * OK: input=a), balanced?=false
 * OK: input=(a(b(c[1]{2(3 4)}))), balanced?=true
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class BalancedBraceCheckExample {

  public static void main(String[] args) {
    demo("", true);
    demo("a", true);
    demo("(a)", true);
    demo("([{}])", true);
    demo("([{]})", false);
    demo("[({]})", false);
    demo("(a", false);
    demo("a)", false);
    demo("(a(b(c[1]{2(3 4)})))", true);
  }

  public static void demo(String input, boolean expectedToBeBalanced) {
    if (expectedToBeBalanced != isBalanced(input)) {
      throw new AssertionError("ERROR: for input=" + input);
    }

    System.out.println("OK: input=" + input + ", balanced?=" + expectedToBeBalanced);
  }

  private static final Map<Character, Character> CLOSE_BRACES_MATCH = Collections
      .unmodifiableMap(new HashMap<Character, Character>() {
        {
          put(')', '(');
          put('}', '{');
          put(']', '[');
        }
      });

  private static boolean isBalanced(String input) {
    final Deque<Character> bracesDeque = new ArrayDeque<>();
    for (int i = 0; i < input.length(); ++i) {
      final char ch = input.charAt(i);
      switch (ch) {
        case '(':case '{':case '[':
          bracesDeque.add(ch);
          break;

        case ')':case '}':case ']':
          if (bracesDeque.isEmpty()) {
            return false;
          }

          final char lastCh = bracesDeque.pollLast();
          if (lastCh != CLOSE_BRACES_MATCH.get(ch)) {
            return false;
          }
          break;
      }
    }

    return bracesDeque.isEmpty();
  }
}
