package problems.leet100.challenges.c2020_05.w2;

import java.util.HashMap;
import java.util.Map;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/535/week-2-may-8th-may-14th/3329/
 * <p></p>
 */
public class ImplementTrieSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      Trie obj = new Trie();
      obj.insert("ambivalent");
      boolean param_2 = obj.search("ambivalent");
      boolean param_3 = obj.startsWith("ambi");
      System.out.printf("param_2 = %s, param_3 = %s\n", param_2, param_3);
    }
  }

  private static final class Trie {

    private static final class Node {
      private final Map<Character, Node> children = new HashMap<>();
      private boolean word;
    }

    private final Node root = new Node();

    /** Initialize your data structure here. */
    public Trie() {

    }

    /** Inserts a word into the trie. */
    public void insert(String word) {
      Node n = root;
      for (int i = 0; i < word.length(); ++i) {
        char ch = word.charAt(i);
        n = n.children.compute(ch, (k, v) -> v == null ? new Node() : v);
      }
      n.word = true;
    }

    /** Returns if the word is in the trie. */
    public boolean search(String word) {
      Node n = lookup(word);
      return n != null && n.word;
    }

    /** Returns if there is any word in the trie that starts with the given prefix. */
    public boolean startsWith(String prefix) {
      return lookup(prefix) != null;
    }

    private Node lookup(String prefix) {
      Node n = root;
      for (int i = 0; i < prefix.length(); ++i) {
        n = n.children.get(prefix.charAt(i));
        if (n == null) {
          break;
        }
      }
      return n;
    }
  }
}
