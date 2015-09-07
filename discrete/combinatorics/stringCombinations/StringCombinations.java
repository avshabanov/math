import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Sample run:
 *
 * <code>
 * Input=, combinations=[]
 * Input=0, combinations=[0]
 * Input=1, combinations=[1]
 * Input=0101, combinations=[0101]
 * Input=1?0?1, combinations=[10001, 10011, 11001, 11011]
 * Input=1??, combinations=[100, 101, 110, 111]
 * Input=???, combinations=[000, 001, 010, 011, 100, 101, 110, 111]
 * </code>
 *
 * @author Alexander Shabanov
 */
public class StringCombinations {

  public static void main(String[] args) {
    demo("");
    demo("0");
    demo("1");
    demo("0101");
    demo("1?0?1");
    demo("1??");
    demo("???");
  }

  private static void demo(String input) {
    final List<String> combinations = findCombinations(input);
    System.out.println("Input=" + input + ", combinations=" + combinations);
  }

  //
  // Solution
  //

  private static List<String> findCombinations(String input) {
    if (input.isEmpty()) {
      return Collections.singletonList(input); // may be an exception as well
    }

    final List<String> accumulator = new ArrayList<>();
    final StringBuilder temp = new StringBuilder(input.length());
    findNext(accumulator, temp, input, 0);
    return accumulator;
  }

  private static void findNext(List<String> accumulator, StringBuilder temp, String input, int pos) {
    if (pos >= input.length()) {
      accumulator.add(temp.toString());
      return;
    }

    final char ch = input.charAt(pos);
    final int len = temp.length();

    switch (ch) {
      case '0':
      case '1':
        temp.append(ch);
        findNext(accumulator, temp, input, pos + 1);
        temp.setLength(len); // remove last element
        return;

      case '?':
        temp.append('0');
        findNext(accumulator, temp, input, pos + 1);
        temp.setLength(len);

        temp.append('1'); // TODO: can be moved to the set of allowable characters
        findNext(accumulator, temp, input, pos + 1);
        temp.setLength(len);
        break;

      default:
        throw new IllegalArgumentException("Illegal character=" + ch);
    }
  }
}
