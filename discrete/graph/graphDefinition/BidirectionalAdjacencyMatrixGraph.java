import java.util.BitSet;

/**
 * A graph, built on top of adjacency matrix.
 */
public final class BidirectionalAdjacencyMatrixGraph implements BidirectionalGraph {
  final int vertexCount;
  final BitSet matrix;

  public BidirectionalAdjacencyMatrixGraph(int vertexCount) {
    this.vertexCount = vertexCount;
    // Potential optimization - ladder matrix, would require (vertexCount * (vertexCount + 1)) / 2 elements
    this.matrix = new BitSet(vertexCount * vertexCount);
  }

  @Override
  public int getVertexCount() {
    return vertexCount;
  }

  @Override
  public boolean isConnected(int from, int to) {
    checkVertex(from, "from");
    checkVertex(to, "to");

    return this.matrix.get(from * vertexCount + to);
  }

  @Override
  public Graph edge(int from, int to, boolean exists) {
    checkVertex(from, "from");
    checkVertex(to, "to");

    this.matrix.set(from * vertexCount + to, exists);
    this.matrix.set(to * vertexCount + from, exists);
    return this;
  }

  private void checkVertex(int vertex, String name) {
    if (vertex < 0 || vertex >= vertexCount) {
      throw new IllegalArgumentException("Vertex " + name + "=" + vertex + " is outside of the allowed bounds");
    }
  }
}
