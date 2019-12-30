package problems.leet100.longestValidParentheses;

/**
 * 32. Longest Valid Parentheses
 * <p>Given a string containing just the characters '(' and ')',
 * find the length of the longest valid (well-formed) parentheses substring.</p>
 */
public class LongestValidParenthesesSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(")()())");
      demo("(()");
    }
  }

  private static void demo(String s) {
    System.out.printf("Input=%s\nOutput=%d\n---\n", s, longestValidParentheses(s));
  }

  private static int longestValidParentheses(String s) {
    int maxLength = 0;
    for (int i = 0; i < s.length(); ++i) {
      final char ch = s.charAt(i);
      if (ch == '(') {
        final int currentLength = longestValidParenthesesWithPrecedingOpenBrace(s, i + 1);
        maxLength = Math.max(maxLength, currentLength);
        i += currentLength; // skip current parentheses group
      }
    }
    return maxLength;
  }

  private static int longestValidParenthesesWithPrecedingOpenBrace(String s, int offset) {
    int openBracesCount = 1;
    for (int i = offset; i < s.length(); ++i) {
      final char ch = s.charAt(i);
      switch (ch) {
      case '(':
        ++openBracesCount;
        continue;
      case ')':
        --openBracesCount;
        if (openBracesCount == 0) {
          int currentLength = i - offset + 2;
          // try to look ahead and see if there is another subsequence right after this one that could be matched
          int next = i + 1;
          if (next < s.length() && s.charAt(next) == '(') {
            currentLength += longestValidParenthesesWithPrecedingOpenBrace(s, next + 1);
          }
          return currentLength;
        }
        continue;
      default:
        throw new IllegalArgumentException("Unexpected character " + ch);
      }
    }
    return 0;
  }
}
