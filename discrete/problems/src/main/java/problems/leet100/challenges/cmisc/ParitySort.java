package problems.leet100.challenges.cmisc;

import java.util.Arrays;

/**
 * Sort Array By Parity
 * Given an array A of non-negative integers, return an array consisting of all the even elements of A, followed by all the odd elements of A.
 *
 * You may return any answer array that satisfies this condition.
 */
class ParitySort {
  private static int[] sortArrayByParity(int[] a) {
    final Integer[] arr = Arrays.stream(a).boxed().toArray(Integer[]::new);
    Arrays.sort(arr, (l, r) -> {
      if (l % 2 == 0) {
        if (r % 2 == 0) {
          return Integer.compare(l, r);
        }
        return -1;
      }

      if (r % 2 == 0) {
        return 1;
      }
      return Integer.compare(l, r);
    });
    return Arrays.stream(arr).mapToInt(i -> i).toArray();
  }
}
