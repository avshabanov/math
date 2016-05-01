import java.util.Arrays;
import java.util.BitSet;
import java.util.HashSet;
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
public final class LockScreenPatternCountAdvExample {
  private static final boolean DBG_STEPS_ENABLED = Boolean.valueOf(System.getProperty("debug"));

  public static void main(String[] args) {
    demo(1, 2);
    demo(2, 1);
    demo(1, 3);
    demo(1, 4);
    demo(2, 2);
    demo(3, 2);
    demo(3, 3);
  }

  static void demo(int width, int height) {
    System.out.println("Count of lock pattern combinations in area " + width + "x" + height +
        " is " + getLockPatternCombinations(width, height));
  }

  static long getLockPatternCombinations(int width, int height) {
    final Set<Edge> edges = getEdges(width, height);
    return getLockPatternCombinations(width, height, edges);
  }

  static long getLockPatternCombinations(int width, int height, Set<Edge> edges) {
    final LockPatternFinder finder = new LockPatternFinder(width, height, edges);
    finder.doCount();
    return finder.counter;
  }

  static final class LockPatternFinder {
    static final long REPORT_THRESHOLD_STEP = 10000000;

    final int vertexCount;
    final Edge[] edges;
    final BitSet visitedEdges;
    long counter;

    public LockPatternFinder(int width, int height, Set<Edge> edges) {
      this.vertexCount = width * height;
      this.edges = edges.toArray(new Edge[edges.size()]);
      this.visitedEdges = new BitSet(vertexCount * vertexCount);
    }

    void doCount() {
      long reportThreshold = REPORT_THRESHOLD_STEP;
      long startTime = System.currentTimeMillis();

      // deque as an array for performance reasons
      final VertexPos[] vertexStack = new VertexPos[1 + edges.length];
      for (int i = 0; i < vertexStack.length; ++i) {
        vertexStack[i] = new VertexPos();
      }

      final boolean dumpStateEnabled = (vertexCount < 5 && DBG_STEPS_ENABLED);
      final BitSet visitedEdges = new BitSet(vertexCount * vertexCount);

      for (int v = 0; v < vertexCount; ++v) {
        int stackPos = 0;
        vertexStack[stackPos].init(v);

        // explore vertex stack
        LOuter: while (stackPos >= 0) {
          final VertexPos last = vertexStack[stackPos];
          final int vertex = last.vertex;

          for (int i = last.pos; i < edges.length; ++i) {
            final Edge edge = edges[i];
            ++last.pos;

            final int destVertex;
            if (edge.getFrom() == vertex) {
              destVertex = edge.getTo();
            } else if (edge.getTo() == vertex) {
              destVertex = edge.getFrom();
            } else {
              continue;
            }

            final int edgeIndex = getEdgeIndex(destVertex, vertex);
            if (visitedEdges.get(edgeIndex)) {
              continue; // already visited this edge
            }

            visitedEdges.set(edgeIndex, true);
            if (counter == reportThreshold) {
              final long now = System.currentTimeMillis();
              System.out.println(" ... " + counter + " combinations found so far, start vertex=" + v +
                  ", timeDelta=" + (now - startTime) + "ms");
              reportThreshold += REPORT_THRESHOLD_STEP;
              startTime = now;
            }
            ++counter;
            ++stackPos;
            vertexStack[stackPos].init(destVertex);

            // Dump state if we don't have a lot of vertices
            if (dumpStateEnabled) {
              System.out.println(" [DBG] state=" + Arrays
                  .stream(vertexStack)
                  .limit(stackPos + 1)
                  .map(vertexPos -> vertexPos.vertex)
                  .collect(Collectors.toList()));
            }

            continue LOuter;
          }

          --stackPos;
          if (stackPos >= 0) {
            final int removedVertexFrom = vertexStack[stackPos].vertex;
            final int edgeIndex = getEdgeIndex(vertex, removedVertexFrom);
            visitedEdges.set(edgeIndex, false); // restore edges state
          }
        }
      }
    } // do count

    int getEdgeIndex(int from, int to) {
      if (from > to) {
        return from * vertexCount + to;
      }
      return to * vertexCount + from;
    }

    static final class VertexPos {
      int vertex = -1;
      int pos;

      void init(int vertex) {
        this.vertex = vertex;
        this.pos = 0;
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
