import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Complexity: O(n^(4/3)) ~ O(n^1.3333...) < O(n^2)
 */
public final class TwoCubeSumUnopt {

  @SuppressWarnings("UnnecessaryLocalVariable")
  private static List<SolutionEntry> getAllSums(int n) {
    final int cubesN = (int) Math.pow(n, 1 / 3.0);
    if (cubesN <= 0) {
      return Collections.emptyList();
    }
    // + bounds check + make sure cubesN is accurate

    final List<SolutionEntry> entries = new ArrayList<SolutionEntry>();

    for (int ia = 0; ia <= cubesN; ++ia) {
      for (int ib = ia; ib <= cubesN; ++ib) {
        for (int ic = 0; ic <= cubesN; ++ic) {
          for (int id = ic; id <= cubesN; ++id) {
            if (ic == ia || id == ia || ic == ib || id == ib) {
              continue; // skip duplicates
            }

            final int a = ia;
            final int b = ib;
            final int c = ic;
            final int d = id;

            if (((a * a * a) + (b * b * b)) == ((c * c * c) + (d * d * d))) {
              entries.add(new SolutionEntry(a, b, c, d));
            }
          }
        }
      }
    }

    return entries;
  }

  public static void main(String[] args) {
    final List<SolutionEntry> entries = getAllSums(100000);
    System.out.println("entries = " + entries);
  }
}
