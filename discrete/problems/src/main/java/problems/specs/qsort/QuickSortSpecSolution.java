package problems.specs.qsort;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;

/**
 * Quick sort implementation using informal Lamport spec as a basis:
 *
 * <code>
 *
 * Init:      A   =   any array of numbers of length N
 *        ⋀   U   =   { [0, N-1] }
 *
 * Next:      U != {}
 *        ⋀   ∃ (b, t) ∈ U:
 *              IF b != t
 *                THEN    ∃ p ∈ [b..(t-1)] :
 *                              A' ∈ Partitions(A, p, b, t)
 *                      ⋀       U' =  (U \ {[b, t]}) ∪ {[b, t], [p + 1, t]}
 *                ELSE    A' =  A
 *                      ⋀ U' =  U \ {[b, t]}
 * </code>
 */
public class QuickSortSpecSolution {

  public static void main(String[] args) {
    demo(new int[] { 2, 3, 4, 1 });

    if (Arrays.asList(args).contains("-demo")) {
      return;
    }

    demo(new int[] { 3, 2, 1 });
    demo(new int[] { 2, 3, 1 });
    demo(new int[] { 8, 6, 2, 3, 4, 1, 7, 9 });
    demo(new int[] { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 });
    demo(new int[] { 9, 8, 7, 6, 5, 4, 3, 2, 1, 0 });
    demo(new int[] { 9, 0, 8, 1, 7, 2, 6, 3, 5, 4 });
    demo(new int[] { 0, 9, 1, 8, 2, 7, 3, 6, 4, 5 });
  }

  private static void demo(int[] nums) {
    final String input = Arrays.toString(nums);
    qsort(nums);
    System.out.printf("Input:  %s\nOutput: %s\n---\n", input, Arrays.toString(nums));
  }

  private static void qsort(int[] nums) {
    if (nums.length < 2) {
      return;
    }

    final Deque<IntPair> u = new ArrayDeque<>();
    u.add(new IntPair(0, nums.length - 1)); // u = { <0, n - 1> }
    while (!u.isEmpty()) {
      final IntPair pair = u.pollFirst(); // u' = u with <b, t> removed
      //System.out.printf("\t[DBG] <--- poll pair=%s\n", pair);

      int p = partition(nums, pair);

      // u' = u with (b, t) removed and (b, p), (p + 1, t) added
      IntPair.addIfNotEmpty(u, pair.b, p);
      IntPair.addIfNotEmpty(u, p + 1, pair.t);

      //System.out.printf("\t[DBG] nums=%s; deque=%s\n", Arrays.toString(nums), u);
    }
  }

  private static int partition(int[] nums, IntPair pair) {
    final int pivot = nums[(pair.b + pair.t) / 2];
    // Hoare's partition scheme
    for (int i = pair.b, j = pair.t;;) {
      while (nums[i] < pivot) { ++i; }
      while (nums[j] > pivot) { --j; }
      if (i >= j) {
        return j; // Exists p in b..(t-1) => pick any partition
      }
      swap(nums, i, j);
    }
  }

  private static void swap(int[] nums, int i, int j) {
    final int temp = nums[i];
    nums[i] = nums[j];
    nums[j] = temp;
  }

  private static final class IntPair {
    final int b;
    final int t;

    IntPair(int b, int t) {
      if (b >= t) {
        throw new IllegalArgumentException(String.format("b >= t for b=%d and t=%d", b, t));
      }
      this.b = b;
      this.t = t;
    }

    static void addIfNotEmpty(Collection<IntPair> pairs, int b, int t) {
      // b != t => b >= t as empty array will produce n - 1 = 0 - 1 = -1
      if (b >= t) { return; } // small optimization to avoid further checks
      pairs.add(new IntPair(b, t));
    }

    @Override public String toString() { return "[" + b + ", " + t + ']'; }
  }
}
