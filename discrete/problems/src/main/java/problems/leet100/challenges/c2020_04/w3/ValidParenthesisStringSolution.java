package problems.leet100.challenges.c2020_04.w3;

import java.util.BitSet;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/530/week-3/3301/
 * <p>Given a string containing only three types of characters: '(', ')' and '*', write a function to check whether
 * this string is valid. We define the validity of a string by these rules:
 *
 * Any left parenthesis '(' must have a corresponding right parenthesis ')'.
 * Any right parenthesis ')' must have a corresponding left parenthesis '('.
 * Left parenthesis '(' must go before the corresponding right parenthesis ')'.
 * '*' could be treated as a single right parenthesis ')' or a single left parenthesis '(' or an empty string.
 * An empty string is also valid.
 *
 * The string size will be in the range [1, 100].</p>
 */
public class ValidParenthesisStringSolution {

  public static void main(String[] args) {
    demo(true, "()");
    demo(true, "(*)");
    demo(true, "(*))");
    demo(false, "(*)))");
    demo(false, ")");
    demo(false, "())");
    demo(false, "(");
    demo(false, "((");
  }

  private static void demo(boolean expected, String s) {
    //boolean b = checkValidStringBruteForce(s);
    boolean b = checkValidStringDP(s);
    if (b != expected) {
      throw new AssertionError("Expectation failed for s=" + s);
    }
    System.out.printf("Input: %s\nOutput: %s\n", s, b);
  }

  private static boolean checkValidStringBruteForce(String s) {
    return checkValidStringBruteForce(s, 0, 0);
  }

  private static boolean checkValidStringBruteForce(String s, int start, int balance) {
    for (int i = start; i < s.length(); ++i) {
      final char ch = s.charAt(i);
      switch (ch) {
      case '(':
        ++balance;
        break;
      case ')':
        --balance;
        if (balance < 0) {
          return false;
        }
        break;
      case '*':
        // three options here: closing brace, open brace, empty char
        if (checkValidStringBruteForce(s, i + 1, balance + 1)) { /* open brace */
          return true;
        }
        if (checkValidStringBruteForce(s, i + 1, balance - 1)) { /* close brace */
          return true;
        }
        // continue, assuming no character at all
        break;
      default:
        throw new IllegalArgumentException("invalid char=" + ch);
      }
    }
    return balance == 0;
  }

  /*
  Let dp[i][j] be true if and only if the interval s[i], s[i+1], ..., s[j] can be made valid.
  Then dp[i][j] is true only if:

  s[i] is '*', and the interval s[i+1], s[i+2], ..., s[j] can be made valid;

  or, s[i] can be made to be '(', and there is some k in [i+1, j] such that s[k] can be made to be ')', plus the two
  intervals cut by s[k] (s[i+1: k] and s[k+1: j+1]) can be made valid;
   */
  private static boolean checkValidStringDP(String s) {
    int n = s.length();
    if (n == 0) return true;
    boolean[][] dp = new boolean[n][n];

    for (int i = 0; i < n; i++) {
      if (s.charAt(i) == '*') dp[i][i] = true;
      if (i < n-1 &&
          (s.charAt(i) == '(' || s.charAt(i) == '*') &&
          (s.charAt(i+1) == ')' || s.charAt(i+1) == '*')) {
        dp[i][i+1] = true;
      }
    }

    for (int size = 2; size < n; size++) {
      for (int i = 0; i + size < n; i++) {
        if (s.charAt(i) == '*' && dp[i + 1][i + size]) {
          dp[i][i+size] = true;
        } else if (s.charAt(i) == '(' || s.charAt(i) == '*') {
          for (int k = i+1; k <= i+size; k++) {
            if ((s.charAt(k) == ')' || s.charAt(k) == '*') &&
                (k == i + 1 || dp[i + 1][k - 1]) &&
                (k == i + size || dp[k + 1][i + size])) {
              dp[i][i + size] = true;
              break;
            }
          }
        }
      }
    }
    return dp[0][n-1];
  }

  private static boolean checkValidString2(String s) {
    if (s.isEmpty()) {
      return true;
    }
    final int len = s.length();
    final BitSet dp = new BitSet(len * len);

    for (int i = 0; i < len; ++i) {
      final char ch = s.charAt(i);
      if (ch == '(') {
        dp.set(i * len + i);
      }

      if (i < len - 1 && (ch == '(' || ch == '*') && (s.charAt(i + 1) == ')' || s.charAt(i + 1) == '*')) {
        dp.set(i * len + i + 1);
      }
    }

    for (int size = 2; size < len; ++size) {
      for (int i = 0; i + size < len; ++i) {
        final char ch = s.charAt(i);
        if (ch == '*' && dp.get(len * (i + 1) + i + size)) {
          dp.set(i * len + i + size);
        } else if (ch == '(' || ch == '*') {
          for (int k = i+1; k <= i+size; k++) {
            if ((s.charAt(k) == ')' || s.charAt(k) == '*') &&
                (k == i + 1 || dp.get(len * (i + 1) + k - 1)) &&
                (k == i + size || dp.get(len * (k + 1) + i + size))) {
              dp.set(len * i + i + size);
            }
          }
        }
      }
    }

    return dp.get(len - 1);
  }

  private static boolean checkValidStringGreedy(String s) {
    int lo = 0, hi = 0;
    for (char c: s.toCharArray()) {
      lo += c == '(' ? 1 : -1;
      hi += c != ')' ? 1 : -1;
      if (hi < 0) break;
      lo = Math.max(lo, 0);
    }
    return lo == 0;
  }
}
