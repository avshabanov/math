import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;


/**
 * Sample run:
 * <pre>
 * Count of lock pattern combinations in area 1x2 is 2
 * Count of lock pattern combinations in area 2x1 is 2
 * Count of lock pattern combinations in area 1x3 is 6
 * Count of lock pattern combinations in area 2x2 is 228
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class LockScreenPatternCountExample {

  public static void main(String[] args) {
    demo(1, 2);
    demo(2, 1);
    demo(1, 3);
    demo(2, 2);
    demo(3, 2);
    demo(3, 3);
  }

  static void demo(int width, int height) {
    System.out.println("Count of lock pattern combinations in area " + width + "x" + height +
        " is " + getLockPatternCombinations(width, height, getEdges(width, height)));
  }

  static long getLockPatternCombinations(int width, int height, Set<Edge> edges) {
    final LockPatternFinder finder = new LockPatternFinder(width, height, edges);
    finder.doCount();
    return finder.counter;
  }

  static final class LockPatternFinder {
    static final long REPORT_THESHOLD_STEP = 10000000;
    final int width;
    final int height;
    final List<Edge> edges;
    long counter;
    long reportThreshold = REPORT_THESHOLD_STEP;
    long startTime = System.currentTimeMillis();
    int currentVertex;

    public LockPatternFinder(int width, int height, Set<Edge> edges) {
      this.width = width;
      this.height = height;
      this.edges = new ArrayList<>(edges);
    }

    void doCount() {
      for (int w = 0; w < width; ++w) {
        for (int h = 0; h < height; ++h) {
          currentVertex = w + width * h;
          searchFromCoord(w, h);
        }
      }
    }

    void searchFromCoord(int w, int h) {
      final int vertex = h * width + w;
      final List<Edge> targets = edges
          .stream()
          .filter(edge -> edge.getFrom() == vertex || edge.getTo() == vertex)
          .collect(Collectors.toList());

      for (final Edge edge : targets) {
        edges.remove(edge);
        ++counter;
        if (counter > reportThreshold) {
          final long now = System.currentTimeMillis();
          System.out.println(" ... " + counter + " combinations found so far, start vertex=" + currentVertex +
              ", timeDelta=" + (now - startTime) + "ms");
          reportThreshold += REPORT_THESHOLD_STEP;
          startTime = now;
        }

        final int destVertex = (edge.getTo() == vertex ? edge.getFrom() : edge.getTo());
        final int wd = destVertex % width;
        final int wh = destVertex / width;
        searchFromCoord(wd, wh);

        edges.add(edge);
      }
    }
  }

  //
  // Private
  //

  private static Set<Edge> getEdges(int width, int height) {
    final Set<Edge> result = new HashSet<>();

    for (int w = 0; w < width; ++w) {
      for (int h = 0; h < height; ++h) {
        addReachableEdges(w, h, width, height, result);
      }
    }

    return result;
  }

  private static void addReachableEdges(int x, int y, int width, int height, Set<Edge> edges) {
    final int fromVertex = y * width + x;

    for (int w = 0; w < width; ++w) {
      for (int h = 0; h < height; ++h) {
        if (w == x && y == h) {
          continue;
        }

        final int dx = Math.abs(x - w);
        final int dy = Math.abs(y - h);
        if (gcd(dx, dy) > 1) {
          continue;
        }

        final int toVertex = h * width + w;
        edges.add(new Edge(fromVertex, toVertex));
      }
    }
  }

  private static int gcd(int a, int b) {
    while (b > 0) {
      final int temp = b;
      b = a % b; // % is remainder
      a = temp;
    }
    return a;
  }

  /**
   * Edges in pattern graph:
   *
   * <pre>
   * (0)  (1)  (2)
   * (3)  (4)  (5)
   * (6)  (7)  (8)
   * </pre>
   *
   * So, the following vertexes are reachable from vertex 0: 1, 3, 4, 7, 5
   */
  private static final class Edge {
    private final int from;
    private final int to;

    public Edge(int from, int to) {
      this.from = Math.min(from, to);
      this.to = Math.max(from, to);
    }

    public int getFrom() {
      return from;
    }

    public int getTo() {
      return to;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;

      final Edge edge = (Edge) o;

      return from == edge.from && to == edge.to;

    }

    @Override
    public int hashCode() {
      int result = from;
      result = 31 * result + to;
      return result;
    }

    @Override
    public String toString() {
      return "[" + from + " - " + to + ']';
    }
  }
}
