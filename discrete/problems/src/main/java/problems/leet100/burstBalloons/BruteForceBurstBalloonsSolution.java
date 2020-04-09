package problems.leet100.burstBalloons;

import com.google.common.base.Stopwatch;

import java.util.Arrays;
import java.util.concurrent.TimeUnit;

/**
 * 312. Burst Balloons
 * https://leetcode.com/problems/burst-balloons/
 * <p>Given n balloons, indexed from 0 to n-1.
 * Each balloon is painted with a number on it represented by array nums.
 * You are asked to burst all the balloons.
 * If the you burst balloon i you will get nums[left] * nums[i] * nums[right] coins.
 * Here left and right are adjacent indices of i.
 * After the burst, the left and right then becomes adjacent.
 * </p><p>
 * Find the maximum coins you can collect by bursting the balloons wisely.
 * </p><p>
 * Note:
 * </p><p>
 * You may imagine nums[-1] = nums[n] = 1. They are not real therefore you can not burst them.
 * 0 ≤ n ≤ 500, 0 ≤ nums[i] ≤ 100</p>
 */
public class BruteForceBurstBalloonsSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(10, 2);
      demo(2, 1, 2);
      demo(1,2,3,1000);
      demo(1000,3,2,1);
      demo(1000,1,2,3);
      demo(1,2,1000,3);
      demo(1,1000,2,3);
      demo(3,1,5,8);
      demo(1,2);
      demo(1,2,3,4);
      demo(4,3,2,1);
      demo(1,2,3,4,5);
      demo(5,4,3,2,1);
      demo(1,2,3,4,5,6);
      demo(1,2,3,4,5,6,7);
      demo(1,2,3,4,5,6,7,8);
      demo(1,2,3,4,5,6,7,8,9);
      demo(1,2,3,4,5,6,7,8,9,8);
//      demo(1,2,3,4,5,6,7,8,9,8,7);                  // t=     5
//      demo(1,2,3,4,5,6,7,8,9,8,7,6);                //        7
//      demo(1,2,3,4,5,6,7,8,9,8,7,6,5);              //        27
//      demo(1,2,3,4,5,6,7,8,9,8,7,6,5,4);            //        102
//      demo(2,4,8,4,0,7,8,9,1,2,4,7,1,7,3);          //        388
//      demo(2,4,8,4,0,7,8,9,1,2,4,7,1,7,3,2);        //        1454
//      demo(2,4,8,4,0,7,8,9,1,2,4,7,1,7,3,2,1);      //        5552
//      demo(2,4,8,4,0,7,8,9,1,2,4,7,1,7,3,2,1,2);    //        19781
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      demo(1,2,3,4,5);
      demo(5,4,3,2,1);
      demo(1,4,3,2,5);
      demo(2,1,3,4,5);
      demo(4,2,3,1,5);
      demo(5,1,2,3,4);
      demo(4,5,1,2,3);
      demo(5,4,1,2,3);
    }
  }

  public static final class Demo3 {
    public static void main(String[] args) {
      demo(10,20,30,40,50,60,70);
    }
  }

  private static void demo(int... nums) {
    final Stopwatch stopwatch = Stopwatch.createStarted();
    final int solution = maxCoins(nums);
    final long elapsedMillis = stopwatch.elapsed(TimeUnit.MILLISECONDS);
    System.out.printf(
        "[%5d ms] maxSum=%7d for nums=%s\n",
        elapsedMillis,
        solution,
        Arrays.toString(nums)
    );
  }

  // Empirical complexity is ~O(4^n)
  private static int maxCoins(int[] nums) {
    if (nums.length == 0) {
      return 0;
    }
    final CoinNodes nodes = new CoinNodes(nums);
    nodes.tryScan(nodes.nodes[0]);
    return nodes.foundMaxSum;
  }

  private static final class CoinNode {
    private static final CoinNode SENTINEL = new CoinNode(-1, 1);

    final int pos;
    final int value;
    CoinNode left = SENTINEL;
    CoinNode right = SENTINEL;

    CoinNode(int pos, int value) {
      this.pos = pos;
      this.value = value;
    }

    boolean isSentinel() {
      return this == SENTINEL;
    }

    @Override
    public String toString() {
      return isSentinel() ? "<sentinel>" : String.format("{#%d -> %d}", pos, value);
    }
  }

  private static final class CoinNodes {
    final CoinNode[] nodes;
    int foundMaxSum = 0;
    int accumulatedMaxSum = 0;

    final int[] entries;
    int entriesPos;

    CoinNodes(int[] nums) {
      this.nodes = new CoinNode[nums.length];
      this.entries = new int[nums.length];
      CoinNode left = CoinNode.SENTINEL;
      for (int i = 0; i < nums.length; ++i) {
        final CoinNode node = new CoinNode(i, nums[i]);
        this.nodes[i] = node;
        node.left = left;
        left.right = node;
        left = node;
      }
    }

    void tryScan(final CoinNode candidate) {
      for (CoinNode n = candidate; !n.isSentinel(); n = n.right) {
        final CoinNode left = n.left;
        final CoinNode right = n.right;

        final int sumElement = left.value * n.value * right.value;
        this.accumulatedMaxSum += sumElement;
        this.entries[this.entriesPos] = n.pos;
        this.entriesPos++;

        final CoinNode next = left.isSentinel() ? right : left;
        if (!next.isSentinel()) {
          // exclude this node
          n.right.left = n.left;
          n.left.right = n.right;

          tryScan(next);

          // recover left and right links; also restore found max sum
          n.right.left = n;
          n.left.right = n;
        } else if (this.entriesPos == this.entries.length) {
          // this is the final node
          this.foundMaxSum = Math.max(this.foundMaxSum, this.accumulatedMaxSum);
        }

        this.accumulatedMaxSum -= sumElement;
        this.entriesPos--;
      }
    }
  }
}
