package problems.leet100.challenges.c2020_05.w1;

import java.util.HashSet;
import java.util.Set;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/534/week-1-may-1st-may-7th/3317/
 * <p>You're given strings J representing the types of stones that are jewels, and S representing the stones you have.
 * Each character in S is a type of stone you have.  You want to know how many of the stones you have are also jewels.
 *
 * The letters in J are guaranteed distinct, and all characters in J and S are letters.
 * Letters are case sensitive, so "a" is considered a different type of stone from "A".</p>
 */
public class JewelsAndStonesSolution {

  public static final class Demo1 {
    public static void main(String[] args) {

    }
  }

  private static int numJewelsInStones(String j, String s) {
    final Set<Character> characterSet = new HashSet<>();
    for (int i = 0; i < j.length(); ++i) {
      characterSet.add(j.charAt(i));
    }

    int result = 0;
    for (int i = 0; i < s.length(); ++i) {
      if (characterSet.contains(s.charAt(i))) {
        ++result;
      }
    }
    return result;
  }
}
