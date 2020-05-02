package problems.leet100.challenges.c2020_04.w1;

import java.util.Arrays;

/**
 * https://leetcode.com/explore/featured/card/30-day-leetcoding-challenge/528/week-1/3283/
 *
 * <p>
 * Given a non-empty array of integers, every element appears twice except for one. Find that single one.
 *
 * Note:
 * Your algorithm should have a linear runtime complexity. Could you implement it without using extra memory?
 * </p>
 */
public class SingleNumberSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(2, 2, 1);
      demo(4, 1, 2, 1, 2);
      demo(1,2,4,-3,1,2,-3);
      demo(17,12,5,-6,12,4,17,-5,2,-3,2,4,5,16,-3,-4,15,15,-4,-5,-6);
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {

      // should be -92
      demo(10,186,-49,176,118,167,-61,189,6,-24,7,-93,71,112,187,45,-36,38,82,108,-46,112,51,165,-37,159,1,-53,7,38,90,181,-23,91,-42,172,-95,130,84,149,-47,68,126,-67,175,22,121,131,84,114,60,64,182,-75,-17,-71,69,-92,103,-91,-91,86,126,166,33,-36,-80,-37,118,-80,-18,127,36,-71,-82,-82,144,12,57,149,71,91,-83,-100,-30,45,186,16,-51,-72,-83,107,140,-97,-93,1,12,189,-61,-50,180,98,96,-29,193,167,57,-45,16,6,-76,4,109,-23,22,144,190,-97,193,-51,-99,-79,-47,142,107,175,109,121,190,90,34,32,63,-24,41,-53,41,89,130,-18,-99,103,86,127,-30,102,32,-49,181,-60,114,60,-29,182,-75,168,96,51,33,142,108,69,10,-57,166,48,82,161,-17,-50,102,63,-45,140,180,176,-95,36,-46,168,187,161,-72,-100,-42,165,-76,-67,89,159,64,34,98,4,-60,172,-79,68,48,131,-57);
    }
  }

  private static void demo(int... nums) {
    System.out.printf("Input: %s\nOutput: %d\n---\n", Arrays.toString(nums), singleNumber(nums));
  }

  // simpler solution: use XORs
  private static int singleNumber(int[] nums) {
    // find minimum value which would act as a sentinel value in ad-hoc inplace hash table
    int min = nums[0];
    int countOfMins = 1;
    for (int i = 1; i < nums.length; ++i) {
      final int n = nums[i];
      if (min > n) {
        min = n;
        countOfMins = 1;
      } else if (min == n) {
        ++countOfMins;
      }
    }
    if (countOfMins == 1) {
      return min; // shortcut: min element appears odd times in the array
    }

    // create a hash table off of the array
    int result = min;
    int offset = 0;
    for (boolean repeat = true; repeat;) {
      repeat = false;
      int movedCount = 0;
      for (int i = 0; i < nums.length; ++i) {
        final int x = nums[i];
        if (x == min) {
          continue; // skip mins
        }
        result = x;

        // put a value into desired slot
        final int nextPos = posHash(x, offset, nums.length);
        if (nextPos == i) {
          continue; // the number is where it should be
        }

        // at this point we know for sure that we need to repeat due to hash table collisions / move operations
        repeat = true;

        final int val = nums[nextPos];
        if (val == x) {
          // duplicate found: reset both values to a sentinel value
          nums[nextPos] = min;
          nums[i] = min;
          ++movedCount;
          continue;
        }
        if (val == min) {
          // move current value to a dedicated position
          nums[nextPos] = x;
          nums[i] = min;
          ++movedCount;
          continue;
        }

        // replace a value only if it is not legitimately there
        final int valPos = posHash(val, offset, nums.length);
        if (valPos != nextPos) {
          // replace values
          nums[i] = val;
          nums[nextPos] = x;
          ++movedCount;
        }
      }

      if (movedCount == 0) {
        ++offset; // break hash collisions to make things move
      }
    }


    return result;
  }

  private static int posHash(int x, int offset, int length) {
    return (length + ((x + offset) % length)) % length;
  }
}
