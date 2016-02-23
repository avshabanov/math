import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Shabanov
 */
public interface Graph {

  int getVertexCount();

  boolean isConnected(int from, int to);

  Graph edge(int from, int to, boolean exists);

  default int length(int from, int to) {
    if (from == to) {
      return 0;
    }

    if (isConnected(from, to)) {
      return 1;
    }

    return Integer.MAX_VALUE;
  }

  default List<Integer> getAdjacentVertices(int from) {
    final List<Integer> result = new ArrayList<>();
    final int vertexCount = getVertexCount();

    for (int i = 0; i < vertexCount; ++i) {
      if (isConnected(from, i)) {
        result.add(i);
      }
    }

    return result;
  }
}
