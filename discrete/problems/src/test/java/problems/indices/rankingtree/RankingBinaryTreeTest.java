package problems.indices.rankingtree;

import org.junit.Test;
import problems.indices.rankingtree.impl.RankingBinaryTree;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ThreadLocalRandom;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

public final class RankingBinaryTreeTest extends RankingTreeTestBase {

  @Test
  public void shouldInsertRandomRange() {
    // Given:
    final RankingTree<Integer, String> t = createTree();
    final int keySetSize = 1000;
    final List<Integer> keys = IntStream.rangeClosed(0, keySetSize - 1)
        .boxed().collect(Collectors.toList());
    Collections.shuffle(keys, ThreadLocalRandom.current());

    // When (inserted first time):
    final List<Integer> sortedKeys = new ArrayList<>(keySetSize);
    for (final Integer n : keys) {
      sortedKeys.add(n);
      Collections.sort(sortedKeys);
      final int pos = Collections.binarySearch(sortedKeys, n);

      final RankedResult<String> r = t.put(n, String.format("val-1-%04d", n));

      // Then:
      assertNull(
          "Old value returned by 'put' shall be null for unique key-value pair",
          r.getValue()
      );
      assertEquals(
          "(First insert) position mismatch for key=" + n,
          pos,
          r.getRank()
      );
      assertEquals(
          "(First insert) size mismatch",
          sortedKeys.size(),
          t.size()
      );
    }

    // Then (must have proper offsets):
    for (final Integer n : keys) {
      final RankedResult<String> r = t.get(n);

      assertEquals(
          "(Lookup after first insert) position mismatch for key=" + n,
          n.intValue(),
          r.getRank()
      );
      assertEquals(
          "(Lookup after first insert) value mismatch for key=" + n,
          String.format("val-1-%04d", n),
          r.getValue()
      );
    }

    // When (overridden):
    for (final Integer n : keys) {
      final RankedResult<String> r = t.put(n, String.format("val-2-%04d", n));

      // Then (overridden result):
      assertEquals(
          "(Lookup after second insert) position mismatch for key=" + n,
          n.intValue(),
          r.getRank()
      );
      assertEquals(
          "(Lookup after second insert) value mismatch for key=" + n,
          String.format("val-1-%04d", n),
          r.getValue()
      );
    }
  }

  @Override
  protected <K extends Comparable<K>, V> RankingTree<K, V> createTree() {
    return new RankingBinaryTree<>();
  }
}
