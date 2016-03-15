import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Sample output:
 * <pre>
 * Shuffle input=a, output=a
 * Shuffle input=ab, output=ab
 * Unable to shuffle input=aa, reason=Too many duplicate characters in a string
 * Shuffle input=aabc, output=abac
 * Shuffle input=qqw, output=qwq
 * Unable to shuffle input=qqqw, reason=Too many duplicate characters in a string
 * Shuffle input=ccbb, output=bcbc
 * Shuffle input=qqwqw, output=qwqwq
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class ShuffleSimilarLettersExample {
  public static void main(String[] args) {

    demo("a");
    demo("ab");
    demo("aa");
    demo("aabc");
    demo("qqw");
    demo("qqqw");
    demo("ccbb");
    demo("qqwqw");
  }

  public static void demo(String input) {
    final String output;
    try {
      output = shuffle(input);
      System.out.println("Shuffle input=" + input + ", output=" + output);
    } catch (IllegalArgumentException e) {
      System.out.println("Unable to shuffle input=" + input + ", reason=" + e.getMessage());
    }
  }

  public static String shuffle(String input) {
    final List<CharFrequency> frequencies = getSortedFrequencies(input);

    // create the result
    final StringBuilder sb = new StringBuilder();
    char prevCharacter = 0;
    for (int i = 0; i < input.length(); ++i) {

      // find next candidate character and remove it from frequency list
      char curCharacter = 0;
      boolean curCharacterFound = false;
      for (int j = 0; j < frequencies.size(); ++j) {
        final CharFrequency entry = frequencies.get(j);
        if (i > 0 && prevCharacter == entry.value) {
          continue;
        }

        curCharacter = entry.value;
        curCharacterFound = true;
        entry.count = entry.count - 1;
        if (entry.count == 0) {
          frequencies.remove(j);
        }
        break;
      }

      if (!curCharacterFound) {
        throw new IllegalArgumentException("Too many duplicate characters in a string");
      }

      prevCharacter = curCharacter;
      sb.append(curCharacter);
    }

    return sb.toString();
  }

  private static List<CharFrequency> getSortedFrequencies(String input) {
    final Map<Character, Integer> charFrequencyMap = new HashMap<>();
    for (int i = 0; i < input.length(); ++i) {
      charFrequencyMap.compute(input.charAt(i), (character, value) -> value == null ? 1 : value + 1);
    }

    return charFrequencyMap.entrySet().stream()
            .map(entry -> new CharFrequency(entry.getKey(), entry.getValue()))
            .sorted((o1, o2) -> o2.count - o1.count)
            .collect(Collectors.toList());
  }

  private static final class CharFrequency {
    final char value;
    int count;

    public CharFrequency(char value, int count) {
      this.value = value;
      this.count = count;
    }
  }
}
