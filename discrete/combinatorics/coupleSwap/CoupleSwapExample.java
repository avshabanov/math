import java.util.*;

/**
 * Sample run:
 * <pre>
 * Min number of swaps=0 for entries=
 * Min number of swaps=0 for entries=a
 * Min number of swaps=0 for entries=aa
 * Min number of swaps=1 for entries=aba
 * Min number of swaps=2 for entries=abba
 * Min number of swaps=2 for entries=abba
 * Min number of swaps=3 for entries=aabccdb
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class CoupleSwapExample {

  public static void main(String[] args) {
    demo("");
    demo("a");
    demo("aa");
    demo("aba");
    demo("abba");
    demo("abba");
    demo("aabccdb");
  }

  public static void demo(String entries) {
    System.out.println("Min number of swaps=" + getMinNumberOfSwaps(entries) + " for entries=" + entries);
  }

  public static int getMinNumberOfSwaps(String entries) {
    int numberOfSwaps = 0;

    final List<Character> chars = new ArrayList<>(entries.length());
    for (int i = 0; i < entries.length(); ++i) {
      chars.add(entries.charAt(i));
    }

    final Map<Character, Integer> charIndexMap = new HashMap<>();
    final Set<Character> ignored = new HashSet<>();
    boolean swapped;
    do {
      charIndexMap.clear();
      swapped = false;

      for (int i = 0; i < chars.size(); ++i) {
        final Character ch = chars.get(i);
        if (ignored.contains(ch)) {
          continue;
        }

        final Integer first = charIndexMap.put(ch, i);
        if (first != null) {
          // got next pair - remove and continue
          final int localSwaps = swapCouples(chars, first, i);
          numberOfSwaps += localSwaps;
          ignored.add(ch);
          swapped = true;
          break;
        }
      }
      //System.out.println(" [DBG] chars=" + new String(chars.stream().mapToInt(c -> c).toArray(), 0, chars.size()));
    } while (swapped);

    return numberOfSwaps;
  }

  private static int swapCouples(List<Character> chars, int first, int second) {
    for (int i = second - 1; i >= first; --i) {
      chars.set(i + 1, chars.get(i));
    }
    return second - first - 1;
  }
}
