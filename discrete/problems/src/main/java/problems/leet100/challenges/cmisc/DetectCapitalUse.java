package problems.leet100.challenges.cmisc;

/**
 * Detect Capital
 * Given a word, you need to judge whether the usage of capitals in it is right or not.
 *
 * We define the usage of capitals in a word to be right when one of the following cases holds:
 *
 * All letters in this word are capitals, like "USA".
 * All letters in this word are not capitals, like "leetcode".
 * Only the first letter in this word is capital, like "Google".
 * Otherwise, we define that this word doesn't use capitals in a right way.
 */
public class DetectCapitalUse {

  private static boolean detectCapitalUse(String word) {
    State st = ROOT;
    for (int i = 0; i < word.length() && st != null; ++i) {
      if (Character.isUpperCase(word.charAt(i))) {
        st = st.uppercase;
      } else {
        st = st.lowercase;
      }
    }
    return st != null;
  }

  // State machine root
  private static final State ROOT;

  static {
    ROOT = new State();

    final State lowercase = new State();
    lowercase.lowercase = lowercase;

    final State firstUppercase = new State();

    ROOT.lowercase = lowercase;
    ROOT.uppercase = firstUppercase;

    final State allUppercase = new State();
    allUppercase.uppercase = allUppercase;

    firstUppercase.lowercase = lowercase;
    firstUppercase.uppercase = allUppercase;
  }

  private static final class State {
    State lowercase;
    State uppercase;
  }

  //
  // Leetcode Solution
  // https://leetcode.com/articles/detect-capital/
  //

  private static class RegexSolution {
    public static boolean detectCapitalUse(String word) {
      return word.matches("[A-Z]*|.[a-z]*");
    }
  }
}
