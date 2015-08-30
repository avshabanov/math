import java.util.Arrays;

/**
 * Utility class for sorting demos
 */
public final class SortUtil {
  private SortUtil() {}

  public interface InplaceSortAlgorithm {
    void sort(int[] arr);
  }

  public static void sortAndPrint(InplaceSortAlgorithm algorithm, int[] arr) {
    System.out.println("Unsorted arr=" + Arrays.toString(arr));
    algorithm.sort(arr);
    System.out.println("Sorted   arr=" + Arrays.toString(arr));
    System.out.println("===");
  }

  public static void runStandardFixture(InplaceSortAlgorithm algorithm) {
    sortAndPrint(algorithm, new int[]{33, 48, 25, 12, 36, 19, 45});
    sortAndPrint(algorithm, new int[]{3, 2, 1});
    sortAndPrint(algorithm, new int[]{2, 1});
    sortAndPrint(algorithm, new int[]{1, 2});
    sortAndPrint(algorithm, new int[]{1});
    sortAndPrint(algorithm, new int[]{});
  }
}
