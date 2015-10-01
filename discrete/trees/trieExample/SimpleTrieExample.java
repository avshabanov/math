import java.util.ArrayList;
import java.util.List;

/**
 * Simple trie example (prefix trie).
 *
 * Sample output:
 * <code>
 * trie=[[(i: 8), (bow: 6), (bowine: 7), (be: 3), (beg: 4), (begin: 5), (abba: 2), (abberration: 1), (abc: 0)]]
 * words starting with a=[(abba: 2), (abberration: 1), (abc: 0)]
 * words starting with beg=[(beg: 4), (begin: 5)]
 * words starting with abr=[]
 * contains begin?=true
 * contains bowl?=false
 * contains bo?=false
 * </code>
 *
 * @author Alexander Shabanov
 */
public final class SimpleTrieExample {
  public static void main(String[] args) {
    demo1();
  }

  static void demo1() {
    final Dictionary<Integer> dict = new LinkedListBasedTrie<>();
    dict.insert("abc", 0);
    dict.insert("abberration", 1);
    dict.insert("abba", 2);
    dict.insert("be", 3);
    dict.insert("beg", 4);
    dict.insert("begin", 5);
    dict.insert("bow", 6);
    dict.insert("bowine", 7);
    dict.insert("i", 8);

    System.out.println("trie=" + dict);
    System.out.println("words starting with a=" + dict.findWithPrefix("a"));
    System.out.println("words starting with beg=" + dict.findWithPrefix("beg"));
    System.out.println("words starting with abr=" + dict.findWithPrefix("abr"));
    System.out.println("contains begin?=" + dict.contains("begin"));
    System.out.println("contains bowl?=" + dict.contains("bowl"));
    System.out.println("contains bo?=" + dict.contains("bo"));
  }

  //
  // Private
  //

  interface Dictionary<T> {
    interface Entry<T> {
      CharSequence getKey();
      T getValue();
    }

    T insert(CharSequence prefixOrWord, T value);

    boolean contains(CharSequence word); // word assumed to exist if it is associated with non-null value

    List<Dictionary.Entry<T>> findWithPrefix(CharSequence prefix);
  }


  /**
   * Naive Trie Implementation
   *
   * @param <T> A type of the value, associated with the complete word
   */
  private static final class LinkedListBasedTrie<T> implements Dictionary<T> {
    private final TrieNode<T> node = new TrieNode<>();

    @Override
    public T insert(CharSequence word, T value) {
      final int length = word.length();
      TrieNode<T> n = node;
      for (int i = 0; i < length; ++i) {
        final char ch = word.charAt(i);

        // now find an entry that corresponds to the given char
        // possible optimizations: Sorted Array, Sorted Sparse Array, BST, HashTable
        TrieEntry<T> entry = n.entry;
        for (; entry != null; entry = entry.nextEntry) {
          if (entry.ch == ch) {
            break;
          }
        }

        if (entry == null) {
          final TrieEntry<T> newEntry = new TrieEntry<>(ch);
          newEntry.nextEntry = n.entry;
          n.entry = newEntry;
          entry = newEntry;
        }

        n = entry.childNode;
      }

      final T prev = n.value;
      n.value = value;
      return prev;
    }

    @Override
    public boolean contains(CharSequence word) {
      final TrieNode<T> n = findTrieNodeWithPrefix(word);
      return n != null && n.value != null;
    }

    @Override
    public List<Entry<T>> findWithPrefix(CharSequence prefix) {
      final List<Entry<T>> result = new ArrayList<>();
      final StringBuilder buffer = new StringBuilder();
      buffer.append(prefix);
      findAllWords(findTrieNodeWithPrefix(prefix), result, buffer);
      return result;
    }

    @Override
    public String toString() {
      return "[" + findWithPrefix("") + ']';
    }

    //
    // Private
    //

    private static <T> void findAllWords(TrieNode<T> n, List<Entry<T>> result, StringBuilder buffer) {
      if (n == null) {
        return;
      }

      if (n.value != null) {
        result.add(new EntryImpl<>(buffer.toString(), n.value));
      }

      final int len = buffer.length();
      for (TrieEntry<T> e = n.entry; e != null; e = e.nextEntry) {
        buffer.append(e.ch);
        findAllWords(e.childNode, result, buffer);
        buffer.setLength(len); // restore buffer state
      }
    }

    private static final class EntryImpl<T> implements Entry<T> {
      private final CharSequence key;
      private final T value;

      public EntryImpl(CharSequence key, T value) {
        this.key = key;
        this.value = value;
      }

      @Override
      public CharSequence getKey() {
        return key;
      }

      @Override
      public T getValue() {
        return value;
      }

      @Override
      public String toString() {
        return "(" + key + ": " + value + ')';
      }
    }

    private TrieNode<T> findTrieNodeWithPrefix(CharSequence word) {
      final int length = word.length();
      TrieNode<T> n = node;
      for (int i = 0; i < length; ++i) {
        final char ch = word.charAt(i);

        TrieEntry<T> entry = n.entry;
        for (; entry != null; entry = entry.nextEntry) {
          if (entry.ch == ch) {
            break;
          }
        }

        if (entry == null) {
          return null;
        }

        n = entry.childNode;
      }

      return n;
    }
  }

  private static final class TrieNode<T> {
    T value;
    TrieEntry<T> entry;
  }

  private static final class TrieEntry<T> {
    final char ch;
    TrieEntry<T> nextEntry;
    TrieNode<T> childNode = new TrieNode<>();

    public TrieEntry(char ch) {
      this.ch = ch;
    }
  }
}
