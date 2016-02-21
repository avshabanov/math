import java.util.*;

/**
 * Sample run:
 * <pre>
 * Given string= and dictionary=#[] combinations=[]
 * Given string=a and dictionary=#[] combinations=[]
 * Given string= and dictionary=#[a, b] combinations=[]
 * Given string=ab ba and dictionary=#[ab, ba] combinations=[ab ab, ab ba, ba ab, ba ba]
 * Given string=oodr fo aterms and dictionary=#[door, odor, stream, tamers, master, of] combinations=[door of stream, door of tamers, door of master, odor of stream, odor of tamers, odor of master]
 * </pre>
 * @author Alexander Shabanov
 */
public final class ShuffledWordsInStringExample {

  public static void main(String[] args) {
    demo("", new Dictionary(Collections.emptyList()));
    demo("a", new Dictionary(Collections.emptyList()));
    demo("", new Dictionary(Arrays.asList("a", "b")));
    demo("ab ba", new Dictionary(Arrays.asList("ab", "ba")));
    demo("oodr fo aterms", new Dictionary(Arrays.asList("door", "odor", "of", "stream", "master", "tamers")));
  }

  public static void demo(String source, Dictionary dictionary) {
    System.out.println("Given string=" + source + " and dictionary=" + dictionary +
        " combinations=" + findCombinations(source, dictionary));
  }

  public static List<String> findCombinations(String source, Dictionary dictionary) {
    final CombinationFinder finder = new CombinationFinder(source, dictionary);
    if (!finder.find(0)) {
      return Collections.emptyList();
    }
    return Collections.unmodifiableList(finder.getResult());
  }

  public static final class Dictionary {
    private final Map<Key, Set<String>> combinationMap = new HashMap<>();

    public Dictionary(Iterable<String> words) {
      // transform list of words into a map
      for (final String word : words) {
        final Key key = new Key(word);
        Set<String> combinations = combinationMap.get(key);
        if (combinations == null) {
          combinations = new HashSet<>();
          combinations.add(word);
          combinationMap.put(key, combinations);
        } else {
          combinations.add(word);
        }
      }

      // seal values
      for (final Map.Entry<Key, Set<String>> entry : combinationMap.entrySet()) {
        final Set<String> value = entry.getValue();
        entry.setValue(Collections.unmodifiableSet(value));
      }
    }

    public Collection<String> getCombinations(CharSequence word) {
      final Set<String> result = combinationMap.get(new Key(word));
      return result != null ? result : Collections.emptyList();
    }

    @Override
    public String toString() { // NOTE: Not required for solution, this is just a nice-to-have feature
      final StringBuilder result = new StringBuilder(20 + combinationMap.size() * 10);
      result.append("#[");
      boolean next = false;
      for (final Set<String> value : combinationMap.values()) {
        for (final String str : value) {
          if (next) {
            result.append(", ");
          }
          result.append(str);
          next = true;
        }
      }
      result.append("]");
      return result.toString();
    }

    private static final class Key {
      final char[] chars;

      public Key(CharSequence source) {
        this.chars = source.toString().toCharArray(); // TODO: can be optimized (w/o string conversion)
        Arrays.sort(this.chars);
      }

      @Override
      public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Key)) return false;

        Key key = (Key) o;

        return Arrays.equals(chars, key.chars);

      }

      @Override
      public int hashCode() {
        return Arrays.hashCode(chars);
      }
    }
  }

  //
  // Private
  //

  private static final class CombinationFinder {
    private final String source;
    private final Dictionary dictionary;
    private final StringBuilder builder;
    private final List<String> result;

    CombinationFinder(String source, Dictionary dictionary) {
      this.source = source;
      this.dictionary = dictionary;
      this.builder = new StringBuilder(source.length());
      this.result = new ArrayList<>();
    }

    public List<String> getResult() {
      return result;
    }

    boolean find(int pos) {
      final WordAndWhitespace wordAndWhitespace = getWord(source, pos);
      if (wordAndWhitespace == null) {
        result.add(builder.toString());
        return true;
      }

      final Collection<String> combinations = dictionary.getCombinations(wordAndWhitespace.getWord());
      if (combinations.isEmpty()) {
        return false;
      }

      final int originalLength = builder.length();
      builder.append(wordAndWhitespace.getWhitespace());
      final int whitespaceLength = builder.length();
      for (final String possibleWord : combinations) {
        builder.append(possibleWord);
        if (!find(pos + wordAndWhitespace.length())) {
          return false; // return immediately if solution has not been found
        }
        builder.setLength(whitespaceLength); // return back where the last whitespace ends
      }
      builder.setLength(originalLength); // restore string builder

      return true;
    }
  }

  private static final class WordAndWhitespace {
    final CharSequence whitespace;
    final CharSequence word;

    public WordAndWhitespace(CharSequence whitespace, CharSequence word) {
      this.whitespace = whitespace;
      this.word = word;
    }

    int length() {
      return getWhitespace().length() + getWord().length();
    }

    public CharSequence getWhitespace() {
      return whitespace;
    }

    public CharSequence getWord() {
      return word;
    }
  }

  private static WordAndWhitespace getWord(String source, int pos) {
    int wordStart = -1;
    int i;
    for (i = pos; i < source.length(); ++i) {
      final char ch = source.charAt(i);
      if (ch == ' ') {
        if (wordStart < 0) {
          continue; // word start has not been found yet
        }

        break; // end of the word
      }

      if ((ch < 'a' || ch > 'z') && (ch < 'A' && ch > 'Z')) {
        throw new IllegalArgumentException("Illegal character at pos=" + i);
      }

      if (wordStart < 0) {
        wordStart = i;
      }
    }

    if (wordStart < 0) {
      return null; // no more words (end of string)
    }

    // TODO: can be optimized
    return new WordAndWhitespace(source.substring(pos, wordStart), source.substring(wordStart, i));
  }
}
