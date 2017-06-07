import sun.text.normalizer.Trie;

import java.util.HashMap;
import java.util.Map;

/**
 * PROBLEM:
 * <pre>
 * Given two large strings containing arbitrarily large space-separated numbers
 * write a method returning a list of common number entries.
 * </pre>
 *
 *
 * @author Alexander Shabanov
 */
public final class NumbersTrieExample {

  public static void main(String[] args) {
    demo("1 2", "2");
    demo("1 2", "1");
    demo("11 12", "110");
    demo("11 12", "1");
    demo("11 123", "123 1 23 11 1 7 1 1 11 11 123");
  }

  public static void demo(String str1, String str2) {
    final Dictionary dictionary = createDictionary(str1);
    final Map<String, Integer> intersections = getIntersection(str2, dictionary);
    System.out.println("Intersections between str1=" + str1 + " and str2=" + str2 + ":");

    if (intersections.isEmpty()) {
      System.out.println("\t<none>");
    } else {
      for (final Map.Entry<String, Integer> entry : intersections.entrySet()) {
        System.out.println("\t'" + entry.getKey() + "' - " +
            entry.getValue() + " " + (entry.getValue() == 1 ? "entry" : "entries"));
      }
    }
  }

  private static Dictionary createDictionary(CharSequence sequence) {
    final NumericLexeme lexeme = new NumericLexeme(sequence);
    final Dictionary dictionary = new TrieDictionary();
    while (lexeme.moveNext()) {
      dictionary.insert(lexeme);
    }
    return dictionary;
  }

  private static Map<String, Integer> getIntersection(CharSequence sequence, Dictionary dictionary) {
    final NumericLexeme lexeme = new NumericLexeme(sequence);
    final Map<String, Integer> result = new HashMap<>();
    while (lexeme.moveNext()) {
      if (!dictionary.contains(lexeme)) {
        continue;
      }

      final String number = lexeme.toString();
      result.compute(number, (k, v) -> (v == null) ? 1 : v + 1);
    }
    return result;
  }

  private static final class NumericLexeme implements CharSequence {
    final CharSequence origin;
    final int originLength;
    int start;
    int end;

    public NumericLexeme(CharSequence origin) {
      this.origin = origin;
      this.originLength = origin.length();
    }

    @Override
    public int length() {
      return (this.end - this.start);
    }

    @Override
    public char charAt(int index) {
      assert index >= 0 && index < length();
      return this.origin.charAt(this.start + index);
    }

    @Override
    public CharSequence subSequence(int start, int end) {
      return this.origin.subSequence(this.start + start, this.start + end);
    }

    @Override
    public String toString() {
      return this.origin.subSequence(this.start, this.end).toString();
    }

    boolean moveNext() {
      // skip whitespace
      int offset = this.end;
      for (; offset < this.originLength; ++offset) {
        char ch = origin.charAt(offset);
        if (ch != ' ') {
          break;
        }
      }

      // find end of number
      final int nextStart = offset;
      for (; offset < this.originLength; ++offset) {
        char ch = this.origin.charAt(offset);
        if (ch >= '0' && ch <= '9') {
          continue;
        }

        if (ch != ' ') {
          throw new IllegalArgumentException("Illegal char=" + ch);
        }

        break;
      }

      this.start = nextStart;
      this.end = offset;

      return this.start < this.end;
    }
  }

  private static final class TrieNode {
    static final int NUMERIC_CHAR_COUNT = 10;

    final TrieNode[] children = new TrieNode[NUMERIC_CHAR_COUNT];
    boolean complete = false;
  }

  private interface Dictionary {
    void insert(CharSequence sequence);
    boolean contains(CharSequence sequence);
  }

  private static final class TrieDictionary implements Dictionary {
    final TrieNode root = new TrieNode();

    @Override
    public void insert(CharSequence sequence) {
      TrieNode next = this.root;

      for (int i = 0; i < sequence.length(); ++i) {
        final int charIndex = getCheckedCharIndex(sequence, i);

        final TrieNode prev = next;
        next = next.children[charIndex];
        if (next == null) {
          next = new TrieNode();
          prev.children[charIndex] = next;
        }
      }

      if (next != this.root) {
        next.complete = true;
      }
    }

    @Override
    public boolean contains(CharSequence sequence) {
      TrieNode next = root;

      for (int i = 0; i < sequence.length(); ++i) {
        final int charIndex = getCheckedCharIndex(sequence, i);

        next = next.children[charIndex];
        if (next == null) {
          return false;
        }
      }

      return next.complete;
    }

    private static int getCheckedCharIndex(CharSequence sequence, int pos) {
      final char ch = sequence.charAt(pos);
      final int charIndex = ch - '0';

      if (charIndex < 0 || charIndex > TrieNode.NUMERIC_CHAR_COUNT) {
        throw new IllegalArgumentException("Number contains illegal char=" + ch + "(code:" + ((int) ch) + ")");
      }

      return charIndex;
    }
  }
}
