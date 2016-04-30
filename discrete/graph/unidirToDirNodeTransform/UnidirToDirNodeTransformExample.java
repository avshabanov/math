import java.util.*;

/**
 * Sample run:
 * <pre>
 * result=
 *   |  0  1  2
 * --+---------
 * 0 |  0  1  0
 * 1 |  0  0  0
 * 2 |  0  1  0
 *
 * result=
 *   |  0  1  2
 * --+---------
 * 0 |  0  1  0
 * 1 |  0  0  1
 * 2 |  0  0  0
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class UnidirToDirNodeTransformExample {

  public static void main(String[] args) {
    demo1();
    demo2();
  }

  public static void demo1() {
    final BidirectionalGraph graph = new BidirectionalAdjacencyMatrixGraph(3);
    graph.edge(0, 1, true).edge(1, 2, true);

    final UnidirectionalGraph result = toUnidirectional(graph, 1);
    System.out.println("result=\n" + GraphUtil.asString(result));
  }

  public static void demo2() {
    final BidirectionalGraph graph = new BidirectionalSparseGraph();
    graph.edge(0, 1, true).edge(1, 2, true);

    final UnidirectionalGraph result = toUnidirectional(graph, 2);
    System.out.println("result=\n" + GraphUtil.asString(result));
  }


  public static UnidirectionalGraph toUnidirectional(BidirectionalGraph graph, int node) {
    final UnidirectionalGraph result = new UnidirectionalAdjacencyMatrixGraph(graph.getVertexCount());

    final Set<Integer> visitedVertexes = new HashSet<>();
    final Deque<Integer> verticesToProcess = new ArrayDeque<>();
    verticesToProcess.add(node);

    while (!verticesToProcess.isEmpty()) {
      final int n = verticesToProcess.pollLast();
      visitedVertexes.add(n);

      final List<Integer> adjacentVertices = graph.getAdjacentVertices(n);

      //noinspection Convert2streamapi
      for (final Integer adjacentVertex : adjacentVertices) {
        if (!visitedVertexes.contains(adjacentVertex)) {
          result.edge(adjacentVertex, n, true);
          verticesToProcess.add(adjacentVertex);
        }
      }
    }

    return result;
  }
}
