package problems.leet100.challenges.c2020_05.w1;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

/**
 * <p>Suppose you have n versions [1, 2, ..., n] and you want to find out the first bad one, which causes all the
 * following ones to be bad.
 *
 * You are given an API bool isBadVersion(version) which will return whether version is bad.
 * Implement a function to find the first bad version. You should minimize the number of calls to
 * the API.</p>
 */
public class FirstBadVersionSolution {

  public static final class Demo1 {
    public static void main(String[] args) throws Exception {
      final ExecutorService exec = Executors.newFixedThreadPool(2);

      demo(null, 2147483647,  2147483647);
      demo(null,  1702766719, 2126753390);

      demo(exec, 4, 10);
      demo(exec, 4, 15);
      demo(exec, 8, 15);
      for (int n = 5; n < 10; ++n) {
        for (int v = 0; v <= n; ++v) {
          demo(exec, v, n);
        }
      }


      exec.shutdown();
      System.out.println("---");
    }

    private static void demo(ExecutorService exec, int expectedVersion, int n) throws Exception {
      final BadVersionFinder f = new BadVersionFinder(expectedVersion);
      final int actualVersion;
      if (exec != null) {
        final Future<Integer> result = exec.submit(() -> f.firstBadVersion(n));
        actualVersion = result.get(1L, TimeUnit.SECONDS);
      } else {
        actualVersion = f.firstBadVersion(n);
      }

      if (actualVersion != expectedVersion) {
        throw new AssertionError("Mismatch for expectedVersion=" + expectedVersion + " and n=" + n);
      }
      System.out.printf("Input: expectedVersion=%d, n=%d\nOutput: %d\n",
          expectedVersion, n, actualVersion);
    }
  }

  private static class BadVersionFinder {
    final int expectedVersion;

    private BadVersionFinder(int expectedVersion) {
      this.expectedVersion = expectedVersion;
    }

    boolean isBadVersion(int version) {
      return version >= expectedVersion;
    }

    int firstBadVersion(int n) {
      int left = 0;
      int right = n;
      int found = -1;
      while (left <= right) {
        int medium = right - (right - left) / 2;
        if (isBadVersion(medium)) {
          found = medium;
          right = medium - 1;
          continue;
        }

        left = medium + 1;
      }
      return found;
    }
  }
}
