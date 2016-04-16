import java.util.*;

/**
 * Sample run:
 * <pre>
 * A range=(1, 2) is covered by ranges=null in given entries=[]
 * A range=(1, 2) is covered by ranges=[(1, 2)] in given entries=[(1, 2)]
 * A range=(1, 3) is covered by ranges=[(1, 2), (2, 4)] in given entries=[(1, 2), (2, 4)]
 * A range=(1, 3) is covered by ranges=null in given entries=[(1, 2), (3, 4)]
 * A range=(3, 13) is covered by ranges=[(9, 12), (11, 14), (3, 9)] in given entries=[(1, 4), (30, 40), (20, 91), (8, 10), (6, 7), (3, 9), (9, 12), (11, 14)]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class MinSetOfRangesExample {

  public static void main(String[] args) {
    demo(r(1, 2), Collections.emptyList());
    demo(r(1, 2), Collections.singletonList(r(1, 2)));
    demo(r(1, 3), Arrays.asList(r(1, 2), r(2, 4)));
    demo(r(1, 3), Arrays.asList(r(1, 2), r(3, 4)));
    demo(r(3, 13), Arrays.asList(
        r(1, 4), r(30, 40), r(20, 91), r(8, 10), r(6, 7), r(3, 9), r(9, 12), r(11, 14)
    ));
  }

  public static void demo(RangeEntry target, List<RangeEntry> entries) {
    System.out.println("A range=" + target + " is covered by ranges=" + getMinCover(target, entries) +
        " in given entries=" + entries);
  }

  //
  // Solution
  //

  public static List<RangeEntry> getMinCover(RangeEntry target, List<RangeEntry> entries) {
    final Finder finder = new Finder(target, entries);
    finder.find(new ArrayList<>(entries.size()), 0);
    return finder.ranges == null ? null : new ArrayList<>(finder.ranges);
  }


  private static final class Finder {
    private Set<RangeEntry> ranges = null;
    private final RangeEntry target;
    private final List<RangeEntry> entries;

    public Finder(RangeEntry target, List<RangeEntry> entries) {
      this.target = target;
      this.entries = entries;
    }

    public void find(List<RangeEntry> accumulator, int startIndex) {
      // check if accumulator covers target
      int from = target.from;
      int to = target.to;
      for (final RangeEntry a : accumulator) {
        if (a.from <= from) {
          from = Math.max(from, a.to);
        }

        if (a.to >= to) {
          to = Math.min(to, a.from);
        }
      }

      if (from >= to) {
        // covered, add candidate ranges
        ranges = new HashSet<>(accumulator);
        return;
      }

      for (int i = startIndex; i < entries.size(); ++i) {
        final RangeEntry entry = entries.get(i);
        if (!target.intersects(entry)) {
          continue;
        }

        // binary insert
        int insertIndex = Collections.binarySearch(accumulator, entry, (o1, o2) -> o1.from - o2.from);
        if (insertIndex < 0) {
          insertIndex = -insertIndex - 1;
        }
        accumulator.add(insertIndex, entry);

        find(accumulator, i + 1);

        accumulator.remove(insertIndex);
      }
    }
  }


  //
  // Range Entry definition
  //

  public static RangeEntry r(int from, int to) {
    return new RangeEntry(from, to);
  }

  public static final class RangeEntry {
    private final int from;
    private final int to;

    public RangeEntry(int from, int to) {
      if (from > to) {
        throw new IllegalArgumentException("from=" + from + " is greater than to=" + to);
      }
      this.from = from;
      this.to = to;
    }

    public boolean intersects(RangeEntry other) {
      if (other.from <= from) {
        return other.to > from;
      }
      return other.from < to;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;

      RangeEntry that = (RangeEntry) o;

      return from == that.from && to == that.to;
    }

    @Override
    public int hashCode() {
      int result = from;
      result = 31 * result + to;
      return result;
    }

    @Override
    public String toString() {
      return "(" + from + ", " + to + ')';
    }
  }
}
