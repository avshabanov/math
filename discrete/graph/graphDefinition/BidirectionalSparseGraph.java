import java.util.HashSet;
import java.util.Set;

/**
 * @author Alexander Shabanov
 */
public final class BidirectionalSparseGraph implements BidirectionalGraph {
  private int vertexCount = 0;
  private Set<Entry> edgeSet = new HashSet<>();

  @Override
  public int getVertexCount() {
    return vertexCount;
  }

  @Override
  public boolean isConnected(int from, int to) {
    return edgeSet.contains(new Entry(from, to));
  }

  @Override
  public Graph edge(int from, int to, boolean exists) {
    if (from < 0 || to < 0) {
      throw new IllegalArgumentException("Vertex index can't be negative");
    }

    this.vertexCount = Math.max(vertexCount, from + 1);
    this.vertexCount = Math.max(vertexCount, to + 1);

    if (exists) {
      edgeSet.add(new Entry(from, to));
    } else {
      edgeSet.remove(new Entry(from, to));
    }

    return this;
  }

  //
  // Private
  //

  private static final class Entry {
    final int from;
    final int to;

    public Entry(int from, int to) {
      if (from > to) {
        this.from = from;
        this.to = to;
      } else {
        this.from = to;
        this.to = from;
      }
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof Entry)) return false;

      final Entry entry = (Entry) o;

      return from == entry.from && to == entry.to;

    }

    @Override
    public int hashCode() {
      int result = from;
      result = 31 * result + to;
      return result;
    }
  }
}
