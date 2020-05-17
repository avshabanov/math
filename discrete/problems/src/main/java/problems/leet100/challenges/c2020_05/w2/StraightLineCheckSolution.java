package problems.leet100.challenges.c2020_05.w2;

/**
 * https://leetcode.com/explore/featured/card/may-leetcoding-challenge/535/week-2-may-8th-may-14th/3323/
 * <p>You are given an array coordinates, coordinates[i] = [x, y], where [x, y] represents the coordinate of a point.
 * Check if these points make a straight line in the XY plane.</p>
 * <p>Constraints:
 * 2 <= coordinates.length <= 1000
 * coordinates[i].length == 2
 * -10^4 <= coordinates[i][0], coordinates[i][1] <= 10^4
 * coordinates contains no duplicate point.</p>
 */
public class StraightLineCheckSolution {

  public static final class Demo1 {

    public static void main(String[] args) {
      int[][] coordinates = {{1,2},{2,3},{3,4},{4,5},{5,6},{6,7}};
      final boolean v = checkStraightLine(coordinates);
      System.out.println("v = " + v);
    }
  }

  private static boolean checkStraightLine(int[][] coordinates) {
    if (coordinates.length == 0) {
      return true;
    }

    double ratio = 0;
    int[] pair0 = coordinates[0];

    for (int i = 1; i < coordinates.length; ++i) {
      // normalize order
      int[] left;
      int[] right;
      if (pair0[0] > coordinates[i][0]) {
        left = coordinates[i];
        right = pair0;
      } else {
        left = pair0;
        right = coordinates[i];
      }

      // special case: all dots are on the straight vertical line
      if (left[0] == right[0]) {
        if (i > 1) {
          return false;
        }

        for (int j = i + 1; j < coordinates.length; ++j) {
          if (left[0] != coordinates[j][0]) {
            return false;
          }
        }

        break;
      }

      // more general case: arbitrary line, compute K
      double currentRatio = (right[1] - left[1]) / (double) (right[0] - left[0]);
      if (i > 1) {
        // use proper double comparison taking into an account epsilon factor
        if (Math.abs(currentRatio - ratio) > EPSILON) {
          return false;
        }
      } else {
        ratio = currentRatio;
      }
    }

    return true;
  }

  private static final double EPSILON = 0.00000001;
}
