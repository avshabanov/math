
/**
 * Sample run:
 * <pre>
 * Testing word= palindrome?=true
 * Testing word=c palindrome?=true
 * Testing word=cc palindrome?=true
 * Testing word=cd palindrome?=false
 * Testing word=cdc palindrome?=true
 * Testing word=cdd palindrome?=false
 * Testing word=civic palindrome?=true
 * Testing word=civdc palindrome?=false
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class PalindromeCheckExample {

  public static void main(String[] args) {
    test("", true);
    test("c", true);
    test("cc", true);
    test("cd", false);
    test("cdc", true);
    test("cdd", false);
    test("civic", true);
    test("civdc", false);
  }

  static void test(String word, boolean palindromeExpected) {
    if (isPalindrome(word) != palindromeExpected) {
      throw new AssertionError("Expectation error - for word=" + word + " palindromeExpected=" + palindromeExpected);
    }

    System.out.println("Testing word=" + word + " palindrome?=" + palindromeExpected);
  }

  //
  // Private
  //

  private static boolean isPalindrome(String word) {
    final int length = word.length();
    final int palindromeLetterCount = length / 2;
    for (int i = 0; i < palindromeLetterCount; ++i) {
      final char left = word.charAt(i);
      final char right = word.charAt(length - i - 1);
      if (left != right) {
        return false;
      }
    }
    return true;
  }
}
