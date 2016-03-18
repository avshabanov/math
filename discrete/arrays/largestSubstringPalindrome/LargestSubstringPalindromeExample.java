/**
 * Sample output:
 * <pre>
 * Largest substring palindrome= in input=
 * Largest substring palindrome=a in input=a
 * Largest substring palindrome=a in input=abc
 * Largest substring palindrome=aba in input=aba
 * Largest substring palindrome=aba in input=abac
 * Largest substring palindrome=aba in input=tabac
 * Largest substring palindrome=tabat in input=tabat
 * Largest substring palindrome=abba in input=qabbapp
 * </pre>
 * 
 * @author Alexander Shabanov
 */
public final class LargestSubstringPalindromeExample {

  public static void main(String[] args) {
    demo("");
    demo("a");
    demo("abc");
    demo("aba");
    demo("abac");
    demo("tabac");
    demo("tabat");
    demo("qabbapp");
  }

  private static void demo(String input) {
    System.out.println("Largest substring palindrome=" + getLargestSubstringPalindrome(input) + " in input=" + input);
  }

  private static String getLargestSubstringPalindrome(String input) {
    for (int len = input.length(); len > 0; --len) {
      for (int start = 0;; ++start) {
        final int end = start + len;
        if (end > input.length()) {
          break;
        }

        if (isPalindrome(input, start, end)) {
          return input.substring(start, end);
        }
      }
    }

    return "";
  }

  private static boolean isPalindrome(String input, int start, int end) {
    final int mid = (start + end) / 2;
    for (int k = 0; k < mid; ++k) {
      final char left = input.charAt(start++);
      final char right = input.charAt(--end);
      if (left != right) {
        return false;
      }
    }
    return true;
  }
}
