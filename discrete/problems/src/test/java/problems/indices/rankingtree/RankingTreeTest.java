package problems.indices.rankingtree;

import org.junit.Test;
import problems.indices.rankingtree.impl.RankingTreeImpl;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

public final class RankingTreeTest {

  @Test
  public void shouldHandleEmptyLookup() {
    final RankingTree<String, Integer> tree = new RankingTreeImpl<>();
    assertNull(tree.get("something"));
    assertEquals(0, tree.size());
  }

  @Test
  public void shouldPutAndRetrieve() {
    final RankingTree<String, Integer> tree = new RankingTreeImpl<>();
    RankedResult<Integer> r = tree.put("one", 1);
    assertEquals("Insertion result", RankedResult.of(0, null), r);

    r = tree.get("one");
    assertEquals("Retrieval result", RankedResult.of(0, 1), r);

    assertEquals(1, tree.size());
  }

  @Test
  public void shouldOverwrite() {
    final RankingTree<Long, String> tree = new RankingTreeImpl<>();
    tree.put(1L, "one");
    RankedResult<String> r = tree.put(1L, "uno");
    assertEquals("Overwrite result", RankedResult.of(0, "one"), r);
    assertEquals(1, tree.size());

    r = tree.get(1L);
    assertEquals("Retrieval result", RankedResult.of(0, "uno"), r);
  }
}
