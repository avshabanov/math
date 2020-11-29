package problems.leet100.challenges.cmisc2;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Multiple Solutions
 */
public class MultipleSolutions {

  /*
  Sliding Window Maximum
  You are given an array of integers nums, there is a sliding window of size k which is moving from the very left of
  the array to the very right. You can only see the k numbers in the window. Each time the sliding window moves
  right by one position.

  Return the max sliding window.

  Constraints:

  1 <= nums.length <= 10^5
  -10^4 <= nums[i] <= 10^4
  1 <= k <= nums.length
  */
  public static final class MaxSlidingWindowSolution {

    private static int[] maxSlidingWindow(int[] nums, int k) {
      if (nums == null || nums.length < 1 || k < 1) {
        return new int[0];
      }
      if (k == 1) {
        return nums;
      }
      if (k >= nums.length) {
        return new int[]{Arrays.stream(nums).max().orElseThrow(AssertionError::new)};
      }

      final TreeSet<Item> window = new TreeSet<>();
      for (int i = 0; i < k; i++) {
        window.add(new Item(nums[i], i));
      }

      final int[] result = new int[nums.length - k + 1];
      int resultPos = 0;
      for (int i = k; i < nums.length; i++) {
        result[resultPos] = Objects.requireNonNull(window.last()).num;
        resultPos++;
        final int tailPos = i - k;
        window.remove(new Item(nums[tailPos], tailPos));
        window.add(new Item(nums[i], i));
      }
      result[resultPos] = Objects.requireNonNull(window.last()).num;
      return result;
    }

    private static final class Item implements Comparable<Item> {
      final int num;
      final int pos;

      Item(int num, int pos) {
        this.num = num;
        this.pos = pos;
      }

      @Override public int compareTo(Item o) {
        final int r = Integer.compare(num, o.num);
        return r != 0 ? r : Integer.compare(pos, o.pos);
      }

      @Override public String toString() { return String.format("(#%d)[%d]", pos, num); }
    }

    private static void demo(int[] nums, int k) {
      System.out.printf(
          "Input: %s, k=%d\nOutput: %s\n",
          Arrays.toString(nums),
          k,
          Arrays.toString(maxSlidingWindow(nums, k))
      );
    }

    public static void main(String[] args) {
      demo(new int[]{10,30,-10,-30,50,30,60,70}, 3);
      demo(new int[]{9,11}, 2);
    }
  }

  public static final class PermuteUniqueSolution {

    public static List<List<Integer>> permuteUnique(int[] nums) {
      if (nums == null || nums.length == 0) {
        return Collections.emptyList();
      }
      final Accum accum = new Accum(Arrays.stream(nums).boxed().collect(Collectors.toList()));
      accum.permute(0);
      return new ArrayList<>(accum.result);
    }

    private static final class Accum {
      private final Set<List<Integer>> result = new HashSet<>();
      private final List<Integer> numbers;

      public Accum(List<Integer> numbers) {
        this.numbers = numbers;
      }

      public void permute(int index) {
        if (result.contains(numbers)) {
          return;
        }

        result.add(new ArrayList<>(numbers));

        for (int i = index; i < numbers.size(); i++) {
          final int num = numbers.get(i);
          for (int j = i + 1; j < numbers.size(); j++) {
            if (num == numbers.get(j)) {
              continue; // don't swap identical numbers
            }

            numbers.set(i, numbers.get(j));
            numbers.set(j, num);

            permute(i);

            numbers.set(j, numbers.get(i));
            numbers.set(i, num);
          }
        }
      }
    }

    public static void main(String[] args) {
      System.out.println(permuteUnique(new int[]{1, 2, 3}));
      System.out.println(permuteUnique(new int[]{1, 1, 2}));
      System.out.println(permuteUnique(new int[]{1, 1, 2, 2}));
    }
  }
}
