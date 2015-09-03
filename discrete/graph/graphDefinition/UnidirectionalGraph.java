import java.util.ArrayList;
import java.util.List;

/**
 * Simple unidirectional graph definition, each vertex is an integer from 0 to n
 *
 * @author Alexander Shabanov
 */
public interface UnidirectionalGraph {
  int getVertexCount();

  boolean isConnected(int from, int to);

  UnidirectionalGraph edge(int from, int to, boolean exists);

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
