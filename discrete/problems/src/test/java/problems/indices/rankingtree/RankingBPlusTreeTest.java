package problems.indices.rankingtree;

import problems.indices.rankingtree.impl.RankingBPlusTree;

public final class RankingBPlusTreeTest extends RankingTreeTestBase {

  @Override
  protected <K extends Comparable<K>, V> RankingTree<K, V> createTree() {
    return new RankingBPlusTree<>();
  }
}
