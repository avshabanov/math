package problems.leet100.challenge528.w2;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/529/week-2/3299/
 * <p>
 * You are given a string s containing lowercase English letters, and a matrix shift, where shift[i] = [direction, amount]:
 * direction can be 0 (for left shift) or 1 (for right shift).
 * amount is the amount by which string s is to be shifted.
 * A left shift by 1 means remove the first character of s and append it to the end.
 * Similarly, a right shift by 1 means remove the last character of s and add it to the beginning.
 * Return the final string after all operations.
 * </p>
 */
public class StringShiftsSolution {

  public static void main(String[] args) {
    System.out.println("[2] s=" + stringShift("abc", new int[][]{ new int[]{0,1}, new int[]{1,2} }));

    System.out.println("[1] s=" + stringShift("a", new int[][]{}));

    System.out.println("[3] s=" + stringShift("abcdefg", new int[][]{
        new int[]{1,1}, new int[]{1,1}, new int[]{0,2}, new int[]{1,3}
    }));
  }

  private static String stringShift(String s, int[][] shifts) {
    int offset = 0;
    for (int[] shift : shifts) {
      final int adjustment;
      if (shift[0] == 0) {
        adjustment = s.length() - shift[1];
      } else {
        adjustment = shift[1];
      }
      offset = (offset + adjustment) % s.length();
    }

    final char[] chars = new char[s.length()];
    for (int i = 0; i < chars.length; ++i) {
      chars[(i + offset) % chars.length] = s.charAt(i);
    }
    return new String(chars);
  }
}
