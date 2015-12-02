import java.util.List;

/**
 * @author Alexander Shabanov
 */
public interface Graph {

  int getVertexCount();

  boolean isConnected(int from, int to);

  int length(int from, int to);

  Graph edge(int from, int to, boolean exists);

  List<Integer> getAdjacentVertices(int from);
}
