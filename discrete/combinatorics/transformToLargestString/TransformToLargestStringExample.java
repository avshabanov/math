import java.util.*;
import java.util.stream.Collectors;

/**
 * Sample output:
 * <pre>
 * Largest string=abc for input=abc, indices=[]
 * Largest string=bac for input=abc, indices=[(0, 1)]
 * Largest string=cba for input=abc, indices=[(0, 2)]
 * Largest string=cba for input=abc, indices=[(0, 2), (0, 1)]
 * Largest string=dbca for input=abcd, indices=[(0, 3), (0, 1)]
 * Largest string=dcba for input=abcd, indices=[(0, 2), (0, 1), (0, 3)]
 * Largest string=dbca for input=abdc, indices=[(0, 3), (2, 3)]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class TransformToLargestStringExample {

  public static void main(String[] args) {
    demo("abc", new Indices());
    demo("abc", new Indices().add(0, 1));
    demo("abc", new Indices().add(0, 2));
    demo("abc", new Indices().add(0, 2).add(0, 1));
    demo("abcd", new Indices().add(0, 3).add(0, 1));
    demo("abcd", new Indices().add(0, 2).add(0, 1).add(0, 3));
    demo("abdc", new Indices().add(0, 3).add(2, 3)); // original example from PROBLEM.md
  }

  // TODO: add execution trace for swap operations (much harder problem)

  public static void demo(String input, Indices indices) {
    System.out.println("Largest string=" + transformToLargestString(input, indices) + " for input=" + input +
        ", indices=" + indices);
  }

  private static String transformToLargestString(String input, Indices indices) {
    final char[] buf = input.toCharArray();
    final List<List<Integer>> indicesGroup = toIndicesGroup(indices);

    for (final List<Integer> indexList : indicesGroup) {
      // character sorted backwards
      final List<Character> sorted = indexList.stream()
          .map(pos -> buf[pos]).sorted((o1, o2) -> o2 - o1).collect(Collectors.toList());
      for (int i = 0; i < indexList.size(); ++i) {
        buf[indexList.get(i)] = sorted.get(i);
      }
    }

    return new String(buf);
  }

  private static List<List<Integer>> toIndicesGroup(Indices indices) {
    final Map<Integer, Set<Integer>> indicesGroup = new HashMap<>();
    for (final IndexPair indexPair : indices.indexList) {
      final Set<Integer> union = new HashSet<>();
      uniteIndices(indicesGroup, indexPair.left, union);
      uniteIndices(indicesGroup, indexPair.right, union);
    }

    return new HashSet<>(indicesGroup.values())
        .stream()
        .map(indexPairs -> indexPairs.stream().sorted((o1, o2) -> o1 - o2).collect(Collectors.toList()))
        .collect(Collectors.toList());
  }

  private static void uniteIndices(Map<Integer, Set<Integer>> indicesGroup, int index, Set<Integer> union) {
    union.add(index);

    final Set<Integer> other = indicesGroup.get(index); // NOTE: can't use compute here
    if (other == union) {
      return;
    }

    if (other == null) {
      indicesGroup.put(index, union);
      return;
    }

    union.addAll(other);
    indicesGroup.put(index, union);
    for (final int otherIndex : other) {
      uniteIndices(indicesGroup, otherIndex, union);
    }
  }

  private static final class IndexPair {
    final int left;
    final int right;

    public IndexPair(int left, int right) {
      if (left < 0 || right <= left) {
        throw new IllegalArgumentException();
      }
      this.left = left;
      this.right = right;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) {
        return true;
      }
      if (!(o instanceof IndexPair)) {
        return false;
      }
      final IndexPair indexPair = (IndexPair) o;
      return (left == indexPair.left) && (right == indexPair.right);

    }

    @Override
    public int hashCode() {
      return 31 * left + right;
    }

    @Override
    public String toString() {
      return "(" + left + ", " + right + ')';
    }
  }

  private static final class Indices {
    final List<IndexPair> indexList = new ArrayList<>();

    Indices add(int left, int right) {
      if (left == right) {
        return this; // no effect
      }
      this.indexList.add(new IndexPair(left, right));
      return this;
    }

    @Override
    public String toString() {
      return indexList.toString();
    }
  }
}

/*
OLD VERSION:

  private static List<List<IndexPair>> toIndicesGroup(Indices indices) {
    final Map<Integer, Set<IndexPair>> indicesGroup = new HashMap<>();
    for (final IndexPair indexPair : indices.indexList) {
      final Set<IndexPair> union = new HashSet<>();
      union.add(indexPair);
      uniteIndices(indicesGroup, indexPair.left, union);
      uniteIndices(indicesGroup, indexPair.right, union);
    }

    return new HashSet<>(indicesGroup.values())
        .stream()
        .map(indexPairs -> indexPairs.stream().sorted((o1, o2) -> o1.left - o2.left).collect(Collectors.toList()))
        .collect(Collectors.toList());
  }

  private static void uniteIndices(Map<Integer, Set<IndexPair>> indicesGroup, int index, Set<IndexPair> union) {
    final Set<IndexPair> other = indicesGroup.get(index); // NOTE: can't use compute here
    if (other == union) {
      return;
    }

    if (other == null) {
      indicesGroup.put(index, union);
      return;
    }

    union.addAll(other);
    indicesGroup.put(index, union);
    for (final IndexPair otherIndexPair : other) {
      uniteIndices(indicesGroup, otherIndexPair.left, union);
      uniteIndices(indicesGroup, otherIndexPair.right, union);
    }
  }


 */