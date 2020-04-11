package problems.leet100.challenge528.w2;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/529/week-2/3291/
 * <p>Given two strings S and T, return if they are equal when both are typed into empty text editors.
 * # means a backspace character.</p>
 */
public class BackspaceStringCompareSolution {

  public static void main(String[] args) {
    boolean b;
//    b = backspaceCompare("abc", "abc");
//    b = backspaceCompare("", "a#");
//    b = backspaceCompare("b", "ba#");
//    b = backspaceCompare("b", "ca#");
//    b = backspaceCompare("bxj##tw", "bxj###tw");
    b = backspaceCompare("nzp#o#g", "b#nzp#o#g");
    System.out.println("b=" + b);
  }

  private static boolean backspaceCompare(String s, String t) {
    int si = s.length() - 1;
    int ti = t.length() - 1;
    do {
      si = si >= 0 ? predChar(s, si) : si;
      ti = ti >= 0 ? predChar(t, ti) : ti;
      if (si >= 0 && ti >= 0) {
        if (s.charAt(si) != t.charAt(ti)) {
          return false;
        }
        --si;
        --ti;
      }
    } while (si >= 0 && ti >= 0);
    if (si >= 0) {
      si = predChar(s, si);
    }
    if (ti >= 0) {
      ti = predChar(t, ti);
    }
    return si < 0 && ti < 0;
  }

  private static int predChar(String s, int pos) {
    int backspaces = 0;
    for (; pos >= 0; --pos) {
      if (s.charAt(pos) != '#') {
        --backspaces;
        if (backspaces < 0) {
          break;
        }
      } else {
        ++backspaces;
      }
    }
    return pos;
  }
}
