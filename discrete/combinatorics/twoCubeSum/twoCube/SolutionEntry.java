package twoCube;

import java.util.Arrays;

public final class SolutionEntry {
  final long a, b, c, d;

  public SolutionEntry(long a, long b, long c, long d) {
    this.a = a;
    this.b = b;
    this.c = c;
    this.d = d;
  }

  public long[] toSortedArray() {
    final long[] arr = { a, b, c, d };
    Arrays.sort(arr);
    return arr;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof SolutionEntry)) return false;

    SolutionEntry that = (SolutionEntry) o;

    return Arrays.equals(that.toSortedArray(), this.toSortedArray());
  }

  @Override
  public int hashCode() {
    return Arrays.hashCode(this.toSortedArray());
  }

  @Override
  public String toString() {
    return "{ " + a + "^3 + " + b + "^3 = " + c + "^3 + " + d + "^3 }";
  }
}
