package twoCube;

import java.util.*;

/**
 * Complexity: O(n^(4/3)) ~ O(n^1.3333...) < O(n^2)
 */
public final class TwoCubeSumUnopt {

  public static void main(String[] args) {
    final Set<SolutionEntry> entries = getAllSums(100000);
    System.out.println("Entries = " + entries + "\nTotal: " + entries.size());
  }

  private static Set<SolutionEntry> getAllSums(int n) {
    final int cubesN = (int) Math.pow(n, 1 / 3.0);
    if (cubesN <= 0) {
      return Collections.emptySet();
    }
    // + bounds check + make sure cubesN is accurate

    final Set<SolutionEntry> entries = new LinkedHashSet<>();

    for (int a = 0; a <= cubesN; ++a) {
      for (int b = a; b <= cubesN; ++b) {
        for (int c = 0; c <= cubesN; ++c) {
          for (int d = c; d <= cubesN; ++d) {
            if (c == a || d == a || c == b || d == b) {
              continue; // skip duplicates
            }

            if (((a * a * a) + (b * b * b)) == ((c * c * c) + (d * d * d))) {
              entries.add(new SolutionEntry(a, b, c, d));
            }
          }
        }
      }
    }

    return entries;
  }
}
