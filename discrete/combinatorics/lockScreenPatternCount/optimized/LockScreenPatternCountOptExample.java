package optimized;

import java.util.*;
import java.util.stream.Collectors;

/**
 * TODO: fix: this approach is still wrong as symmetric optimization doesn't work the way it is implemented here.
 */
public final class LockScreenPatternCountOptExample {

  public static void main(String[] args) {
    demo(2);
    demo(3);
  }

  static void demo(int size) {
    System.out.println("Count of lock pattern combinations in area " + size + "x" + size +
        " is " + getLockPatternCombinations(size, getEdges(size, size)));
  }

  static long getLockPatternCombinations(int size, Set<Edge> edges) {
    final LockPatternFinder finder = new LockPatternFinder(size, edges);
    finder.doCount();
    return finder.counter;
  }

  static final class LockPatternFinder {
    static final long REPORT_THESHOLD_STEP = 10000000;
    final int size;
    final Set<Edge> edges;
    final List<Integer> sequence = new ArrayList<>();
    long counter;
    long reportThreshold = REPORT_THESHOLD_STEP;
    long startTime = System.currentTimeMillis();
    int currentVertex;

    public LockPatternFinder(int size, Set<Edge> edges) {
      this.size = size;
      this.edges = new HashSet<>(edges);
    }

    void doCount() {
      for (int w = 0; w < size; ++w) {
        for (int h = 0; h < size; ++h) {
          currentVertex = w + size * h;
          sequence.add(currentVertex);
          searchFromCoord(w, h);
          sequence.clear();
        }
      }
    }

    void searchFromCoord(int w, int h) {
      final int vertex = h * size + w;
      final List<Edge> targets = edges
          .stream()
          .filter(edge -> edge.getFrom() == vertex || edge.getTo() == vertex)
          .collect(Collectors.toList());

      final Map<Integer, Long> symmetricCountMap = new HashMap<>(targets.size());

      for (final Edge edge : targets) {


        final int destVertex = (edge.getTo() == vertex ? edge.getFrom() : edge.getTo());
        final Long symmetricCount = symmetricCountMap.get(destVertex);
        if (symmetricCount == null) {
          final int destWidth = destVertex % size;
          final int destHeight = destVertex / size;

          final long counterStart = counter;

          // recursive call
          ++counter;
          edges.remove(edge);
          sequence.add(destVertex);
          searchFromCoord(destWidth, destHeight);
          edges.add(edge);
          report();
          sequence.remove(sequence.size() - 1);

          if (destWidth != destHeight) {
            final int symmetricVertex = destWidth * size + destHeight;
            symmetricCountMap.put(symmetricVertex, (counter - counterStart));
          }
        } else {
          // skip this vertex completely as we can reuse symmetric computation result
          counter += symmetricCount;
        }
      }
    }

    void report() {
      if (counter < reportThreshold) {
        return;
      }

      final long now = System.currentTimeMillis();
      while (counter >= reportThreshold) {
        reportThreshold += REPORT_THESHOLD_STEP;
      }
      System.out.println(" ... " + counter + " combinations found so far, start vertex=" + currentVertex +
          ", timeDelta=" + (now - startTime) + "ms, sequence=" + sequence);
      startTime = now;
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
   *
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
