package problems.leet100.minimizingPermutations;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * <p>
 * In this problem, you are given an integer N, and a permutation, P of the integers from 1 to N,
 * denoted as (a_1, a_2, ..., a_N). You want to rearrange the elements of the permutation into increasing order,
 * repeatedly making the following operation:
 * Select a sub-portion of the permutation, (a_i, ..., a_j), and reverse its order.
 * Your goal is to compute the minimum number of such operations required to return the permutation to increasing order.
 * Signature
 * int minOperations(int[] arr)
 * Input
 * Size N is between 1 and 8
 * Array arr is a permutation of all integers from 1 to N
 * Output
 * An integer denoting the minimum number of operations required to arrange the permutation in increasing order
 * Example
 * If N = 3, and P = (3, 1, 2), we can do the following operations:
 * Select (1, 2) and reverse it: P = (3, 2, 1).
 * Select (3, 2, 1) and reverse it: P = (1, 2, 3).
 * output = 2
 * </p>
 */
public class MinimizingPermutationsSolution {

  static class Solver {
    final int[] arr;
    int permutationsCount;
    final Set<Integer> visitedArrs = new HashSet<>();
    int targetVertex;

    public Solver(final int[] arr) {
      // verify, that given array is retaining declared invariants
      final int[] prototype = IntStream.range(1, arr.length + 1).toArray();
      if (!IntStream.of(prototype).boxed().collect(Collectors.toSet())
          .equals(IntStream.of(arr).boxed().collect(Collectors.toSet()))) {
        throw new IllegalArgumentException();
      }

      // it is sufficient to have `n*(n-1)/2` permutations in total using bubble sort approach using
      // simplest 2-element rotations to "bubble up" elements to yield the desired order
      this.permutationsCount = arr.length * (arr.length - 1) / 2;
      this.arr = Arrays.copyOf(arr, arr.length);
      this.targetVertex = foldArray(prototype);
    }

    private void solve(int moves) {
      Integer vertex = foldArray(arr);
      // 1. no need to visit already visited vertex once again
      // 2. no need to dive deeper than permutationsCount steps that we found earlier
      if (moves >= permutationsCount || visitedArrs.contains(vertex)) {
        return;
      }
      if (vertex == targetVertex) {
        permutationsCount = moves;
        return; // we reached terminal state, try finding other solutions
      }
      visitedArrs.add(vertex);
      for (int subsetSize = 2; subsetSize <= arr.length; ++subsetSize) {
        for (int start = 0; start < (arr.length - subsetSize + 1); ++start) {
          final int end = start + subsetSize;
          rotate(arr, start, end);
          solve(moves + 1);
          rotate(arr, start, end); // restore array
        }
      }
      visitedArrs.remove(vertex); // restore visit state
    }

    private static void rotate(int[] arr, int from, int to) {
      final int half = (to - from) / 2;
      for (int i = 0; i < half; ++i) {
        final int lhs = from + i;
        final int rhs = to - i - 1;
        final int tmp = arr[lhs];
        arr[lhs] = arr[rhs];
        arr[rhs] = tmp;
      }
    }

    private static final int ELEMENT_FOLD_BIT_CAPACITY = 3;
    private static final int MAX_ELEMENT_FOLD = (1 << ELEMENT_FOLD_BIT_CAPACITY) - 1;

    private static int foldArray(int[] arr) {
      assert ELEMENT_FOLD_BIT_CAPACITY * arr.length < 32;

      int result = 0; // 3 * 8 = 24 bit - the size of the array
      for (int i = 0, shift = 1; i < arr.length; ++i, shift <<= ELEMENT_FOLD_BIT_CAPACITY) {
        final int normalizedElement = arr[i] - 1;
        if (normalizedElement < 0 || normalizedElement > MAX_ELEMENT_FOLD) {
          throw new IllegalStateException();
        }
        // position - 3 bits per element
        result += normalizedElement * shift;
      }
      return result;
    }
  }

  static int minOperations(int[] arr) {
    if (arr == null || arr.length <= 1) {
      return 0;
    }
    final Solver solver = new Solver(arr);
    solver.solve(0);
    return solver.permutationsCount;
  }

  //
  // Tests
  //

  public static final class TestRotate {
    public static void main(String[] args) {
      final int[] arr = {1, 2, 3, 4, 5, 6, 7, 8};
      System.out.printf("arr1 = %s\n", Arrays.toString(arr));
      Solver.rotate(arr, 1, 3);
      System.out.printf("arr2 = %s\n", Arrays.toString(arr));
      Solver.rotate(arr, 2, 5);
      System.out.printf("arr3 = %s\n", Arrays.toString(arr));
      Solver.rotate(arr, 0, 8);
      System.out.printf("arr4 = %s\n", Arrays.toString(arr));
    }
  }

  public static final class TestFold {
    public static void main(String[] args) {
      System.out.printf("fold1 = %32s\n", Integer.toBinaryString(fold(1)));
      System.out.printf("fold2 = %32s\n", Integer.toBinaryString(fold(1, 2, 3)));
      System.out.printf("fold3 = %32s\n", Integer.toBinaryString(fold(1, 2, 3, 4, 5, 6, 7, 8)));
      System.out.printf("fold4 = %32s\n", Integer.toBinaryString(fold(8, 2, 3, 4, 5, 6, 1, 7)));
    }

    private static int fold(int... arr) {
      return Solver.foldArray(arr);
    }
  }

  public static final class Demo {
    public static void main(String[] args) {
      // demo output
      demo(7,6,5,4,3,2,1);
      demo(7,6,5,4,3,1,2);
      demo(7,1,6,2,5,3,4);
      demo(4,5,3,1,2);
    }

    private static void demo(int... nums) {
      final String s = Arrays.toString(nums);
      final int n = minOperations(nums);
      System.out.printf("MinPermutations for %s: %d\n", s, n);
    }
  }

  // These are the tests we use to determine if the solution is correct.
  // You can add your own at the bottom, but they are otherwise not editable!
  int test_case_number = 1;
  void check(int expected, int output) {
    boolean result = (expected == output);
    char rightTick = '\u2713';
    char wrongTick = '\u2717';
    if (result) {
      System.out.println(rightTick + " Test #" + test_case_number);
    }
    else {
      System.out.print(wrongTick + " Test #" + test_case_number + ": Expected ");
      printInteger(expected);
      System.out.print(" Your output: ");
      printInteger(output);
      System.out.println();
    }
    test_case_number++;
  }

  void printInteger(int n) {
    System.out.print("[" + n + "]");
  }

  public void run() {

    int[] arr_1 = {1, 2, 5, 4, 3};
    int expected_1 = 1;
    int output_1 = minOperations(arr_1);
    check(expected_1, output_1);

    int[] arr_2 = {3, 1, 2};
    int expected_2 = 2;
    int output_2 = minOperations(arr_2);
    check(expected_2, output_2);

    // more test cases...
    int[] arr_4 = {4,3,2,1};
    int expected_4 = 1;
    int output_4 = minOperations(arr_4);
    check(expected_4, output_4);

    int[] arr_3 = {8,7,6,5,4,3,2,1};
    int expected_3 = 1;
    int output_3 = minOperations(arr_3);
    check(expected_3, output_3);
  }

  public static void main(String[] args) {
    new MinimizingPermutationsSolution().run();
  }
}
