package problems.leet100.challenges.c2020_05.w5;

import java.util.Arrays;
import java.util.stream.Collectors;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/538/week-5-may-29th-may-31st/3345/
 * <p>We have a list of points on the plane.  Find the K closest points to the origin (0, 0).
 * (Here, the distance between two points on a plane is the Euclidean distance.)
 * You may return the answer in any order.  The answer is guaranteed to be unique (except for the order that it is in.)</p>
 * <p>Note:
 * 1 <= K <= points.length <= 10000
 * -10000 < points[i][0] < 10000
 * -10000 < points[i][1] < 10000</p>
 */
public class KClosestPointsToOriginSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(new int[][] {{1, 3}, {-2, 2}}, 1);
      demo(new int[][] {{3, 3}, {5, -1}, {-2, 4}}, 2);
    }
  }

  private static void demo(int[][] points, int k) {
    final String s = Arrays.stream(points).map(Arrays::toString).collect(Collectors.joining());
    final int[][] result = kClosest(points, k);
    System.out.printf(
        "Input: %s\nOutput: %s\n",
        s,
        Arrays.stream(result).map(Arrays::toString).collect(Collectors.joining())
    );
  }

  private static int[][] kClosest(int[][] points, int k) {
    Arrays.sort(points, (p1, p2) -> Integer.compare(distSquare(p1), distSquare(p2)));
    return Arrays.copyOf(points, k);
  }

  private static int distSquare(int[] p) {
    return p[0] * p[0] + p[1] * p[1];
  }
}
