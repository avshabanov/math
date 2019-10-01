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

/**
 * Ranked tree on top of unbalanced (for simplicity) binary search tree.
 *
 * The structure it builds may look as follows:
 * <code>
 *     66 (left subtree size: 0)
 *     124 (left subtree size: 0)
 *    151 (left subtree size: 1)
 *  164 (left subtree size: 3)
 *   207 (left subtree size: 0)
 *      260 (left subtree size: 0)
 *     273 (left subtree size: 1)
 *    400 (left subtree size: 2)
 * 570 (left subtree size: 8)
 *   684 (left subtree size: 0)
 *  687 (left subtree size: 1)
 * </code>
 * In the example above indentation shows root/left/right relations, e.g. node 570 is a root with
 * node 164 to its left and node 687 to its right;
 * consequentially node 164 has node 151 to its left and node 207 to its right, etc.
 */
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
    for (final Integer key : keys) {
      sortedKeys.add(key);
      Collections.sort(sortedKeys);
      final int pos = Collections.binarySearch(sortedKeys, key);

      final RankedResult<String> r = t.put(key, String.format("val-1-%04d", key));

      // Then:
      assertNull(
          "Old value returned by 'put' shall be null for unique key-value pair",
          r.getValue()
      );
      assertEquals(
          "(First insert) position mismatch for key=" + key,
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
    for (final Integer key : keys) {
      final RankedResult<String> r = t.put(key, String.format("val-2-%04d", key));

      // Then (overridden result):
      assertEquals(
          "(Lookup after second insert) position mismatch for key=" + key,
          key.intValue(),
          r.getRank()
      );
      assertEquals(
          "(Lookup after second insert) value mismatch for key=" + key,
          String.format("val-1-%04d", key),
          r.getValue()
      );
    }

    // When (delete elements in random order):
    Collections.shuffle(keys, ThreadLocalRandom.current());
    int size = t.size();
    for (final Integer key : keys) {
      final int pos = Collections.binarySearch(sortedKeys, key);
      sortedKeys.remove(pos);
      final RankedResult<String> r = t.delete(key);

      // Then (delete):
      assertEquals(
          "(Delete) position mismatch for key=" + key,
          pos,
          r.getRank()
      );
      assertEquals(
          "(Delete) value mismatch for key=" + key,
          String.format("val-2-%04d", key),
          r.getValue()
      );
      size--;
      assertEquals(
          "(Delete) tree size should decrease",
          size,
          t.size()
      );
    }
    assertEquals("Tree must be empty once all elements deleted", 0, t.size());
  }

  @Override
  protected <K extends Comparable<K>, V> RankingTree<K, V> createTree() {
    return new RankingBinaryTree<>();
  }
}
