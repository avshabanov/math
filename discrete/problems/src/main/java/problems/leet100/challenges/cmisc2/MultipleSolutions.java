package problems.leet100.challenges.cmisc2;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Multiple Solutions
 */
public class MultipleSolutions {

  public static final class Demo1 {

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
