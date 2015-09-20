import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Sample output:
 * <code>
 * Dictionary=Dictionary{ a=0 c=01 b=1 d=10 }
 * 	Sequence=0011, representations=[aabb, acb]
 * 	Sequence=010101, representations=[ababab, ababc, abadb, abcab, abcc, adbab, adbc, addb, cabab, cabc, cadb, ccab, ccc]
 * Dictionary=Dictionary{ a=0 b=1 }
 * 	Sequence=0011, representations=[aabb]
 * 	Sequence=010101, representations=[ababab]
 * </code>
 *
 * @author Alexander Shabanov
 */
public final class HuffmanEncodingVariationExample {
  public static void main(String[] args) {
    demo1();
    demo2();
  }

  private static void demo1() {
    final Dictionary dictionary = new Dictionary();
    dictionary.insert('a', "0");
    dictionary.insert('b', "1");
    dictionary.insert('c', "01");
    dictionary.insert('d', "10");

    System.out.println("Dictionary=" + dictionary);

    displayPossibleEncodings("0011", dictionary);
    displayPossibleEncodings("010101", dictionary);
  }

  private static void demo2() {
    final Dictionary dictionary = new Dictionary();
    dictionary.insert('a', "0");
    dictionary.insert('b', "1");

    System.out.println("Dictionary=" + dictionary);

    displayPossibleEncodings("0011", dictionary);
    displayPossibleEncodings("010101", dictionary);
  }

  private static void displayPossibleEncodings(String sequence, Dictionary dictionary) {
    System.out.println("\tSequence=" + sequence + ", representations=" + findAllRepresentations(sequence, dictionary));
  }

  //
  // Private
  //

  private static List<String> findAllRepresentations(String sequence, Dictionary dictionary) {
    if (sequence.isEmpty()) {
      return Collections.emptyList();
    }

    final StringBuilder str = new StringBuilder(sequence.length());
    final List<String> result = new ArrayList<>();

    findNext(sequence, 0, dictionary.root, str, result, dictionary);

    return result;
  }

  private static void findNext(String sequence, int sequencePos,
                               Dictionary.Node node,
                               StringBuilder str,
                               List<String> result,
                               Dictionary dictionary) {
    if (sequencePos == sequence.length()) {
      if (node == dictionary.root) {
        result.add(str.toString()); // last node should match sequence's end
      }
      return;
    }

    // find next node
    final char charValue = sequence.charAt(sequencePos);
    final Dictionary.Node next;
    switch (charValue) {
      case '0':
        next = node.nZero;
        break;
      case '1':
        next = node.nOne;
        break;
      default:
        throw new IllegalArgumentException("Invalid character at pos=" + sequencePos + " in sequence=" + sequence);
    }

    if (next == null) {
      return; // dead branch - there is no corresponding value in dictionary
    }

    if (next.ch != null) {
      // symbol matches - try it
      final int len = str.length();
      str.append(next.ch.charValue());
      findNext(sequence, sequencePos + 1, dictionary.root, str, result, dictionary);
      str.setLength(len);
    }

    // now we either tried this symbol or we don't have a character corresponding to the given subsequence - try next
    findNext(sequence, sequencePos + 1, next, str, result, dictionary);
  }

  /**
   * Helper data structure that contains all the encoded characters
   */
  private static final class Dictionary {
    private Node root = new Node();

    void insert(char charValue, String encodingSequence) {
      if (encodingSequence.isEmpty()) {
        throw new IllegalArgumentException("Sequence can't be empty");
      }

      Node node = root;
      for (int i = 0; i < encodingSequence.length(); ++i) {
        final char c = encodingSequence.charAt(i);
        switch (c) {
          case '0':
            if (node.nZero == null) {
              node.nZero = new Node();
            }
            node = node.nZero;
            break;
          case '1':
            if (node.nOne == null) {
              node.nOne = new Node();
            }
            node = node.nOne;
            break;
          default:
            throw new IllegalArgumentException("Illegal character at " + i + " in sequence=" + encodingSequence);
        }
      }

      if (node.ch != null) {
        throw new IllegalArgumentException("Duplicate entry for character=" + charValue +
            " as sequence=" + encodingSequence + " already associated with character=" + node.ch);
      }

      node.ch = charValue;
    }

    //
    // Node in a dictionary
    //

    private static final class Node {
      Character ch;
      Node nZero;
      Node nOne;
    }

    //
    // toString
    //


    @Override
    public String toString() {
      final StringBuilder builder = new StringBuilder(100);
      final StringBuilder sequence = new StringBuilder(100);
      builder.append("Dictionary{");
      appendNext(root, builder, sequence);
      builder.append(" }");
      return builder.toString();
    }

    private static void appendNext(Node node, StringBuilder builder, StringBuilder sequence) {
      if (node == null) {
        return;
      }

      if (node.ch != null) {
        builder.append(' ').append(node.ch.charValue()).append('=').append(sequence);
      }

      final int len = sequence.length();
      sequence.append('0');
      appendNext(node.nZero, builder, sequence);
      sequence.setLength(len);
      sequence.append('1');
      appendNext(node.nOne, builder, sequence);
      sequence.setLength(len);
    }
  }
}
