import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

/**
 * Solution and demo for https://leetcode.com/problems/stream-of-characters/
 *
 * Task:
 * <p>
 * Implement the StreamChecker class as follows:
 * StreamChecker(words): Constructor, init the data structure with the given words.
 * query(letter): returns true if and only if for some k >= 1, the last k characters queried (in order from oldest
 * to newest, including this letter just queried) spell one of the words in the given list.
 * </p>
 *
 * As of <tt>2019-12-12</tt>:
 * <code>
 *  Runtime: 443 ms, faster than 26.15% of Java online submissions for Stream of Characters.
 *  Memory Usage: 85.4 MB, less than 100.00% of Java online submissions for Stream of Characters.
 * </code>
 */
public class StreamOfCharactersExample {

  public static void main(String[] args) {
    demo(new String[]{"cd","f","kl"}, "abcdefghijkl");
  }

  public static void demo(String[] words, String letters) {
    final StreamChecker streamChecker = new StreamChecker(words);
    System.out.printf("For %s:\n", Arrays.asList(words));
    for (int i = 0; i < letters.length(); ++i) {
      final char letter = letters.charAt(i);
      System.out.printf("\tstreamChecker.query(%c) = %b\n", letter, streamChecker.query(letter));
    }
    System.out.println("---");
  }

  private static final class StreamChecker {
    private static final int DEFAULT_MAX_QUERIES_SIZE = 40_000;

    private static final class PNode {
      boolean leaf;
      private final Map<Character, PNode> children = new HashMap<>();
    }

    private final PNode root = new PNode();

    private final PNode[] cursors;
    private int cursorPos;

    private void putWord(String word) {
      final int len = word.length();
      PNode n = root;
      for (int i = 0; i < len; ++i) {
        final char ch = word.charAt(i);
        n = n.children.compute(ch, (ignored, oldValue) -> oldValue != null ? oldValue : new PNode());
      }
      n.leaf = true; // make sure this node signifies the whole word
    }

    public StreamChecker(String[] words) {
      int maxWordSize = 0;
      for (final String word : words) {
        putWord(word);
        maxWordSize = Math.max(maxWordSize, word.length());
      }

      cursors = new PNode[Math.min(maxWordSize, DEFAULT_MAX_QUERIES_SIZE)];
    }

    public boolean query(char letter) {
      if (cursors.length == 0) {
        // always return false when no words have been provided
        return false;
      }

      boolean leafNodeMet = false;

      final int nextCursorPos = (this.cursorPos + 1) % cursors.length;
      this.cursorPos = nextCursorPos;
      this.cursors[nextCursorPos] = root;

      for (int i = 0; i < this.cursors.length; ++i) {
        PNode cursor = this.cursors[i];
        if (cursor == null) {
          continue;
        }

        cursor = cursor.children.get(letter);
        this.cursors[i] = cursor;
        if (cursor == null) {
          continue;
        }

        leafNodeMet |= cursor.leaf;
      }

      return leafNodeMet;
    }
  }
}
