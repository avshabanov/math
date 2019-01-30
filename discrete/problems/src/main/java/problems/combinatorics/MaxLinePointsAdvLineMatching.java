package problems.combinatorics;

import problems.util.math.Ratio;

import java.util.*;

/**
 * Improved version of the brute force solution of
 * https://leetcode.com/problems/max-points-on-a-line/
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
    final Map<LineTrait, PointData> lineTraits = new HashMap<>();

    int result = 0;
    for (int i = 0; i < points.length; ++i) {
      int lineCount = 1;
      Point a = points[i];

      // fold all the points that share the same position
      int j = i + 1;
      for (; j < points.length; ++j, ++lineCount) {
        final Point d = points[j];
        if (d.x != a.x || d.y != a.y) {
          break;
        }

        // optimization: skip duplicate points in the outer loop
        ++i;
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

      // now j should point to the very first point, that doesn't share the same vertical,
      // that is (a, b) form either a slanted or horizontal line
      for (; j < points.length; ++j) {
        final Point b = points[j];
        final Ratio slope = Ratio.of(b.y - a.y, b.x - a.x);
        final Ratio intercept = Ratio.fromInteger(a.y).sub(slope.mul(Ratio.fromInteger(a.x)));

        final LineTrait lineTrait = new LineTrait(slope, intercept);
        final int curLineCount = lineCount;
        final PointData pd = lineTraits.computeIfAbsent(lineTrait, k -> new PointData(a, curLineCount));
        if (pd.origin != a) {
          continue;
        }
        pd.count = pd.count + 1;
      }
    }

    for (final PointData p : lineTraits.values()) {
      if (p.count > result) {
        result = p.count;
      }
    }

    return result;
  }

  private static final class PointData {
    Point origin;
    int count;

    public PointData(Point origin, int count) {
      this.count = count;
      this.origin = origin;
    }
  }

  private static final class LineTrait {
    final Ratio slope;
    final Ratio intercept;

    public LineTrait(Ratio slope, Ratio intercept) {
      this.slope = slope;
      this.intercept = intercept;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof LineTrait)) return false;

      LineTrait lineTrait = (LineTrait) o;

      if (!slope.equals(lineTrait.slope)) return false;
      return intercept.equals(lineTrait.intercept);
    }

    @Override
    public int hashCode() {
      int result = slope.hashCode();
      result = 31 * result + intercept.hashCode();
      return result;
    }

    @Override
    public String toString() {
      return "LineTrait{" + slope + ", " + intercept + '}';
    }
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
