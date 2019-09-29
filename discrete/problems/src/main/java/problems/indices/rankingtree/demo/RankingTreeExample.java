package problems.indices.rankingtree.demo;

import problems.indices.rankingtree.RankedResult;
import problems.indices.rankingtree.RankingTree;
import problems.indices.rankingtree.impl.RankingBPlusTree;

/**
 * TBD
 */
public class RankingTreeExample {

  public static void main(String[] args) {
    final RankingTree t = new RankingBPlusTree();
    RankedResult rr;
    rr = t.put("0002", "two");
    assert rr.getRank() == 0;
    rr = t.get("0002");
    System.out.println("rr=" + rr);
  }
}
