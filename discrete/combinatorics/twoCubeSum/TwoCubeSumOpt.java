import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * TODO: complete
 * Unfinished: use unbalanced ad-hoc tree
 */
public class TwoCubeSumOpt {

  private static final class Node {

  }

  private static List<SolutionEntry> getAllSums(int n) {
    final int cubesN = (int) Math.pow(n, 1 / 3.0);
    if (cubesN <= 0) {
      return Collections.emptyList();
    }
    // + bounds check + make sure cubesN is accurate

    final int cubes[] = new int[cubesN];
    cubes[0] = 1;

    // collect cubes
    for (int i = 1; i < cubesN; ++i) {
      int x = cubes[i - 1];
      cubes[i] = x + 3 * i * i + 3 * i + 1;
    }

    final List<SolutionEntry> entries = new ArrayList<SolutionEntry>();



    return entries;
  }

  public static void main(String[] args) {
    final List<SolutionEntry> entries = getAllSums(10000);
    System.out.println("entries = " + entries);
  }
}
