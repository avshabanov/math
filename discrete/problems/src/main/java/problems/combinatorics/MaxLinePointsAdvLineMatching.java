package problems.combinatorics;

import problems.util.math.Ratio;

import java.util.*;

/**
 * Improved version of the brute force solution of
 * https://leetcode.com/problems/max-points-on-a-line/
 *
 * Current result:
 * <code>
 *   Runtime: 83 ms, faster than 7.84% of Java online submissions for Max Points on a Line.
 * </code>
 */
public final class MaxLinePointsAdvLineMatching {

  public static int maxPoints(Point[] sourcePoints) {
    if (sourcePoints.length < 2) {
      return sourcePoints.length;
    }

    // introduce deterministic order in the point array
    final Point[] points = Arrays.copyOf(sourcePoints, sourcePoints.length);
    Arrays.sort(points, POINT_COMPARATOR);

    // this is to optimize lookup for new lines
    final Map<Ratio, Set<Point>> exclusions = new HashMap<>(sourcePoints.length * 2);

    int result = 0;
    for (int i = 0; i < points.length; ++i) {
      int lineCount = 0;
      Point a = points[i];

      // fold all the points that share the same position
      int j = i;
      for (; (j < points.length) && (POINT_COMPARATOR.compare(a, points[j]) == 0); ++j) {
        ++lineCount;
      }

      // fold all the points that share the same x-coordinate
      int sameVerticalCount = lineCount;
      for (; (j < points.length) && (points[j].x == a.x); ++j) {
        ++sameVerticalCount;
      }

      // sameVerticalCount holds count of the dots sharing the same x=t line
      if (sameVerticalCount > result) {
        result = sameVerticalCount;
      }

      // now j should point to the very first point, that doesn't share the same vertical
      for (; j < points.length; ++j) {
        final Point b = points[j];
        final Ratio ctg = Ratio.of(b.y - a.y, b.x - a.x);
        Set<Point> excludedSet = exclusions.computeIfAbsent(ctg, k -> new TreeSet<>(POINT_COMPARATOR));
        if (!excludedSet.add(b)) {
          continue;
        }

        int currentBLineCount = lineCount + 1;

        for (int z = j + 1; z < points.length; ++z) {
          final Point c = points[z];
          final int dy = c.y - a.y;
          final int dx = c.x - a.x;
          final Ratio otherCtg = Ratio.of(dy, dx);
          if (otherCtg.equals(ctg)) {
            excludedSet.add(c);
            ++currentBLineCount;
          }
        }

        if (currentBLineCount > result) {
          result = currentBLineCount;
        }
      }
    }

    return result;
  }

  private static final Comparator<Point> POINT_COMPARATOR = (l, r) -> {
    if (l.x == r.x) {
      return l.y - r.y;
    }
    return l.x - r.x;
  };

  //
  // Demo
  //

  private static void solve(String input) {
    Point.printSolution(Point.fromJsonArray(input),
        MaxLinePointsAdvLineMatching::maxPoints);
  }

  public static final class Case1 {
    public static void main(String[] args) {
      solve("[[2,2],[1,1],[3,3]]");
    }
  }

  public static final class Case2 {
    public static void main(String[] args) {
      solve("[[-230,324],[-291,141],[34,-2],[80,22],[-28,-134],[40,-23],[-72,-149],[0,-17],[32,-32]," +
          "[-207,288],[7,32],[-5,0],[-161,216],[-48,-122],[-3,39],[-40,-113],[115,-216],[-112,-464],[-72,-149]," +
          "[-32,-104],[12,42],[-22,19],[-6,-21],[-48,-122],[161,-288],[16,11],[39,23],[39,30],[873,-111]]");
    }
  }
}
