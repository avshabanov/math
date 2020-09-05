package problems.leet100.challenges.cmisc;

import java.util.*;

/**
 * Largest Component Size by Common Factor
 * Given a non-empty array of unique positive integers A, consider the following graph:
 *
 * There are A.length nodes, labelled A[0] to A[A.length - 1];
 * There is an edge between A[i] and A[j] if and only if A[i] and A[j] share a common factor greater than 1.
 * Return the size of the largest connected component in the graph.
 */
public class LargestComponentSize {

  private static final int[] PRIMES = {
      2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
      109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
      233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331
  };

  public static List<Integer> factorize(int n) {
    final List<Integer> result = new ArrayList<>();
    for (int prime : PRIMES) {
      if (n % prime == 0) {
        result.add(prime);
      }
    }
    if (result.isEmpty()) {
      result.add(n);
    }
    return result;
  }

  private static final class ComponentGroup {
    final int groupId;
    final Set<Integer> numbers = new HashSet<>();
    final Set<Integer> primes = new HashSet<>();

    public ComponentGroup(int groupId) {
      this.groupId = groupId;
    }

    @Override public String toString() { return numbers.toString(); }
  }

  private static int largestComponentSize(final int[] a) {
    final Map<Integer, ComponentGroup> primeToGroup = new HashMap<>();
    int groupCounter = 0;
    for (final int elem : a) {
      final List<Integer> factors = factorize(elem);
      ComponentGroup currentGroup = null;
      for (final int factor : factors) {
        currentGroup = primeToGroup.get(factor);
        if (currentGroup != null) {
          break;
        }
      }

      if (currentGroup == null) {
        currentGroup = new ComponentGroup(++groupCounter);
      }
      currentGroup.numbers.add(elem);
      currentGroup.primes.addAll(factors);

      for (final int factor : factors) {
        final ComponentGroup foundGroup = primeToGroup.get(factor);
        if (foundGroup != null) {
          if (foundGroup.groupId == currentGroup.groupId) {
            continue;
          }

          currentGroup.primes.addAll(foundGroup.primes);
        }
      }

      for (final int prime : currentGroup.primes) {
        final ComponentGroup otherGroup = primeToGroup.get(prime);
        if (otherGroup != null) {
          if (otherGroup.groupId == currentGroup.groupId) {
            continue;
          }
          currentGroup.numbers.addAll(otherGroup.numbers);
        }
        primeToGroup.put(prime, currentGroup);
      }
    }

    int result = 0;
    for (final ComponentGroup group : primeToGroup.values()) {
      result = Math.max(result, group.numbers.size());
    }
    return result;
  }

  public static final class Demo1 {
    public static void main(String[] args) {
      final int n = largestComponentSize(new int[] {65,35,43,76,15,11,81,22,55,92,31});
      System.out.printf("n=%d\n", n);
    }
  }
}
