package twoCube;

import java.util.*;

/**
 * Optimized version, amortized time complexity is O(n)
 *
 * @author Alexander Shabanov
 */
public final class TwoCubeSumOpt {

  private static Set<SolutionEntry> getAllSums(int n) {
    final int cubesCount = (int) Math.pow(n, 1 / 3.0);
    if (cubesCount <= 0) {
      return Collections.emptySet();
    }
    // + bounds check + make sure cubesN is accurate

    final int cubes[] = new int[cubesCount + 1];
    cubes[0] = 0;
    cubes[1] = 1;

    final Map<Integer, Integer> cubeRoots = new HashMap<>(cubesCount * 2);
    cubeRoots.put(0, 0);
    cubeRoots.put(1, 1);

    // collect cubes
    // complexity: O(cubeRoot(n))
    for (int i = 1; i < cubesCount; ++i) {
      int x = cubes[i];
      final int nextX = x + 3 * i * i + 3 * i + 1;
      cubes[i + 1] = nextX;
      cubeRoots.put(nextX, i + 1); // amortized complexity: O(1)
    }

    final Set<SolutionEntry> entries = new LinkedHashSet<>();

    // complexity: O(cubeRoot(n) ^ 3) == O(n)
    for (int a = 0; a < cubesCount; ++a) {
      for (int b = a; b < cubesCount; ++b) {
        for (int c = 0; c < cubesCount; ++c) {
          if ((a == c) || (b == c)) {
            continue;
          }

          final int dCube = cubes[a] + cubes[b] - cubes[c];
          if (dCube < 0) {
            break; // c^3 exceeds sum of a^3+b^3
          }
          final Integer d = cubeRoots.get(dCube); // amortized complexity is O(1)

          if (d != null) {
            entries.add(new SolutionEntry(a, b, c, d));
          }
        }
      }
    }

    return entries;
  }

  public static void main(String[] args) {
    final Set<SolutionEntry> entries = getAllSums(100000);
    System.out.println("Entries = " + entries + "\nTotal: " + entries.size());
  }
}
