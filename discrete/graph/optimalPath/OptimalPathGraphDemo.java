import java.util.Arrays;
import java.util.stream.IntStream;

/**
 * @author Alexander Shabanov
 */
public final class OptimalPathGraphDemo {

  public static void main(String[] args) {
    System.out.println("== OptimalPathGraph ==");

    final UnidirectionalGraph graph1 = new UnidirectionalAdjacencyMatrixGraph(4);
    graph1
        .edge(0, 1, true)
        .edge(1, 2, true)
        .edge(2, 3, true)
        .edge(3, 2, true);
    demo(graph1, 0);
    demo(graph1, 1);

    final UnidirectionalGraph graph2 = new UnidirectionalAdjacencyMatrixGraph(8);
    graph2
        .edge(0, 1, true)
        .edge(2, 3, true)
        .edge(4, 5, true)
        .edge(6, 7, true);
    demo(graph2, 0);
    demo(graph2, 4);
  }

  //
  // Private
  //

  private static void demo(Graph graph, int source) {
    System.out.println("graph=" + graph + ", source=" + source);
    System.out.println("\t" + dijkstra(graph, source));
    System.out.println("===");
  }

  // implementation

  private static final class Distances {
    final int[] distance;
    final int[] prev;

    public Distances(int[] distance, int[] prev) {
      this.distance = distance;
      this.prev = prev;
    }

    @Override
    public String toString() {
      final String[] distStr = new String[distance.length];
      for (int i = 0; i < distance.length; ++i) {
        distStr[i] = (distance[i] == Integer.MAX_VALUE ? "INFINITY" : Integer.toString(distance[i]));
      }
      return "Distances{" +
          "distance=" + Arrays.asList(distStr) +
          ", prev=" + Arrays.toString(prev) +
          '}';
    }
  }

  private static Distances dijkstra(Graph graph, int source) {
    assert source >= 0 && source < graph.getVertexCount();

    final int count = graph.getVertexCount();

    final int[] vertexSet = new int[count];
    int vertexCount = count;

    final int[] distance = new int[count]; // distance from source to vertex[i]
    final int[] prev = new int[count]; // previous node in optimal path from source

    for (int i = 0; i < count; ++i) {
      distance[i] = Integer.MAX_VALUE;
      prev[i] = -1;
      vertexSet[i] = i;
    }

    distance[source] = 0;

    while (vertexCount != 0) {
      // get element with minimum distance from source and remove it from the vertex set
      int minDistVertexIndex = 0;
      int minDist = distance[vertexSet[minDistVertexIndex]];
      for (int i = 1; i < vertexCount; ++i) {
        final int candidateMinDist = distance[vertexSet[i]];
        if (candidateMinDist < minDist) {
          minDistVertexIndex = i;
          minDist = candidateMinDist;
        }
      }
      --vertexCount;
      final int minVertex = vertexSet[minDistVertexIndex];
      vertexSet[minDistVertexIndex] = vertexSet[vertexCount];

      for (int i : graph.getAdjacentVertices(minVertex)) {
        int alt = distance[minVertex];
        if (alt != Integer.MAX_VALUE) {
          final int len = graph.length(minVertex, i);
          alt += len;
        }

        if (alt < distance[i]) {
          distance[i] = alt;
          prev[i] = minDist;
        }
      }
    }

    return new Distances(distance, prev);
  }
}
