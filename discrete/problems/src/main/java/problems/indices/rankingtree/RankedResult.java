package problems.indices.rankingtree;

/**
 * Represents the result of get or put operation upon ranking tree.
 */
public final class RankedResult<V> {
  private final int rank;
  private final V value;

  private RankedResult(int rank, V value) {
    this.rank = rank;
    this.value = value;
  }

  public static <V> RankedResult<V> of(int rank, V value) {
    return new RankedResult<>(rank, value);
  }

  public int getRank() {
    return rank;
  }

  public V getValue() {
    return value;
  }

  @Override
  public String toString() {
    return "{rank: " + getRank() + ", value: " + getValue() + '}';
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof RankedResult)) return false;

    RankedResult<?> that = (RankedResult<?>) o;

    if (getRank() != that.getRank()) return false;
    return getValue() != null ? getValue().equals(that.getValue()) : that.getValue() == null;
  }

  @Override
  public int hashCode() {
    int result = getRank();
    result = 31 * result + (getValue() != null ? getValue().hashCode() : 0);
    return result;
  }
}
