package problems.leet100.challenges.cmisc;

import java.util.*;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

/**
 * Word Break II
 * Given a non-empty string s and a dictionary wordDict containing a list of non-empty words,
 * add spaces in s to construct a sentence where each word is a valid dictionary word.
 * Return all such possible sentences.
 *
 * Note:
 * The same word in the dictionary may be reused multiple times in the segmentation.
 * You may assume the dictionary does not contain duplicate words.
 */
public final class WordBreakII {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println("Word Break II");

      BiFunction<String, List<String>, List<String>> wordBreak = PrefixTreeSolution::wordBreak;

      System.out.println("00 -> " + wordBreak.apply("catsanddog", Arrays.asList("cat", "cats", "and", "sand", "dog")));
      System.out.println("01 -> " + wordBreak.apply("pineapplepenapple", Arrays.asList("apple", "pen", "applepen", "pine", "pineapple")));
      System.out.println("02 -> " + wordBreak.apply("catsandog", Arrays.asList("cats", "dog", "sand", "and", "cat")));

      System.out.println("03L -> " + wordBreak.apply(
          "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          Arrays.asList(
              "a", "aa", "aaa", "aaaa", "aaaaa", "aaaaaa", "aaaaaaa", "aaaaaaaa", "aaaaaaaaa", "aaaaaaaaaa"
          )
      ));
    }
  }

  private static final class PrefixTreeSolution {
    static List<String> wordBreak(String s, List<String> wordDict) {
      final Set<Integer> sourceChars = s.chars().boxed().collect(Collectors.toSet());
      final Set<Integer> dictChars = String.join("", wordDict).chars().boxed().collect(Collectors.toSet());
      if (!dictChars.containsAll(sourceChars)) {
        return Collections.emptyList();
      }

      final WordBreakAssembler assembler = new WordBreakAssembler(s, wordDict);
      assembler.iterate(0);
      return assembler.words;
    }

    private static final class WordBreakAssembler {
      private final List<String> words = new ArrayList<>();
      private final StringBuilder builder = new StringBuilder();
      private final PrefixTreeNode dict;
      private final String source;

      WordBreakAssembler(String source, List<String> words) {
        this.source = source;
        this.dict = PrefixTreeNode.create(words);
      }

      void iterate(int pos) {
        if (pos >= source.length()) {
          words.add(builder.toString());
          return;
        }

        final int initialLength = builder.length();

        // we're still somewhere in the string and we previously hit end of the word
        if (pos > 0) {
          builder.append(' ');
        }

        PrefixTreeNode it = dict;
        for (int i = pos; i < source.length(); ++i) {
          final char ch = source.charAt(i);
          it = it.children.get(ch);
          if (it == null) {
            // can't continue the search
            break;
          }

          builder.append(ch);
          if (it.endOfWord) {
            iterate(i + 1);
          }
        }

        builder.setLength(initialLength);
      }
    }

    private static final class PrefixTreeNode {
      private final Map<Character, PrefixTreeNode> children = new HashMap<>();
      private boolean endOfWord;

      static PrefixTreeNode create(List<String> wordDict) {
        final PrefixTreeNode root = new PrefixTreeNode();
        for (final String word : wordDict) {
          if (word == null || word.isEmpty()) {
            continue;
          }

          PrefixTreeNode it = root;
          for (int i = 0; i < word.length(); ++i) {
            it = it.children.compute(word.charAt(i), (k, v) -> v == null ? new PrefixTreeNode() : v);
          }
          it.endOfWord = true;
        }
        return root;
      }
    }
  }


}
