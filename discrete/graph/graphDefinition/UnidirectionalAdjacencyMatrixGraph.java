/**
 * @author Alexander Shabanov
 */
public final class UnidirectionalAdjacencyMatrixGraph implements UnidirectionalGraph {
  private final boolean[] adjacencyMatrix;
  private final int vertexCount;

  public UnidirectionalAdjacencyMatrixGraph(int vertexCount) {
    this.vertexCount = vertexCount;
    this.adjacencyMatrix = new boolean[vertexCount * vertexCount];
  }

  @Override
  public int getVertexCount() {
    return vertexCount;
  }

  @Override
  public boolean isConnected(int from, int to) {
    return adjacencyMatrix[getPositionalIndex(from, to)];
  }

  @Override
  public UnidirectionalGraph edge(int from, int to, boolean exists) {
    adjacencyMatrix[getPositionalIndex(from, to)] = exists;
    return this;
  }

  //
  // Private
  //

  private int getPositionalIndex(int from, int to) {
    return from + to * vertexCount;
  }
}
