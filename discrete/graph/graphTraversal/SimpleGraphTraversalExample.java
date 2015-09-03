import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * @author Alexander Shabanov
 */
public final class SimpleGraphTraversalExample {

  public static void main(String[] args) {
    final UnidirectionalGraph graph = new UnidirectionalAdjacencyMatrixGraph(4);
    graph
        .edge(2, 0, true)
        .edge(0, 3, true)
        .edge(0, 1, true)
        .edge(1, 2, true);
    System.out.println("Graph:\n" + GraphUtil.asString(graph));

    final List<List<Integer>> result = findPath(graph, 1, 3);
    System.out.println("Path from 1 to 3 = " + result);
  }

  //
  // Private
  //

  private static List<List<Integer>> findPath(UnidirectionalGraph graph, int from, int to) {
    final PathFinder pathFinder = new PathFinder(graph, to);
    pathFinder.start(from);
    return pathFinder.result;
  }

  static final class PathFinder {
    final UnidirectionalGraph graph;
    final List<List<Integer>> result = new ArrayList<>();
    final int to;

    public PathFinder(UnidirectionalGraph graph, int to) {
      this.graph = graph;
      this.to = to;
    }

    // NOTE: Set+List can be replaced with just LinkedHashSet
    private void findPath(Set<Integer> visitedVertices, List<Integer> interimPath, int currentVertex) {
      if (visitedVertices.contains(currentVertex)) {
        return;
      }

      if (currentVertex == to) {
        final List<Integer> path = new ArrayList<>(interimPath.size() + 1);
        path.addAll(interimPath);
        path.add(to);
        result.add(path);
        return;
      }

      visitedVertices.add(currentVertex);
      interimPath.add(currentVertex);

      for (final Integer i : graph.getAdjacentVertices(currentVertex)) {
        findPath(visitedVertices, interimPath, i);
      }

      interimPath.remove(interimPath.size() - 1);
      visitedVertices.remove(currentVertex);
    }

    void start(int from) {
      findPath(new HashSet<>(), new ArrayList<>(), from);
    }
  }
}
