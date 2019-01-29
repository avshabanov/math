package problems.combinatorics;

import java.math.BigInteger;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Brute-force solution for https://leetcode.com/problems/max-points-on-a-line/
 */
public class MaxLinePoints {

  public static int maxPoints(Point[] points) {
    if (points == null || points.length == 0) {
      return 0;
    }

    final TreeMap<Point, Integer> pointMap = new TreeMap<>(POINT_COMPARATOR);
    for (final Point p : points) {
      Integer value = pointMap.get(p);
      value = 1 + (value != null ? value : 0);
      pointMap.put(p, value);
    }
    final List<PointGroup> orderedPoints = pointMap.entrySet().stream()
        .map(e -> new PointGroup(e.getKey().x, e.getKey().y, e.getValue()))
        .collect(Collectors.toList());

    if (orderedPoints.size() < 2) {
      return points.length; // shortcut for simplest cases
    }

    final Map<Line, Set<PointGroup>> lines = new HashMap<>();

    for (int i = 0; i < orderedPoints.size(); ++i) {
      final PointGroup a = orderedPoints.get(i);
      for (int j = i + 1; j < orderedPoints.size(); ++j) {
        final PointGroup b = orderedPoints.get(j);
        // Use the following line equation: k * x + t * y = 1

        final Line key;
        if (a.x.equals(b.x)) {
          key = new VerticalLine(a.x);
        } else {
          // k = (b.y - a.y) / (b.x - a.x)
          final Ratio k = b.y.sub(a.y).div(b.x.sub(a.x));

          // t = a.y - k * a.x
          final Ratio t = a.y.sub(k.mul(a.x));
          key = new NonVerticalLine(k, t);
        }

        Set<PointGroup> value = lines.get(key);
        if (value == null) {
          value = new HashSet<>();
          value.add(a);
          lines.put(key, value);
        }
        value.add(b);
      }
    }

    int result = 0;
    for (final Map.Entry<Line, Set<PointGroup>> entry : lines.entrySet()) {
      int pointCount = 0;
      for (final PointGroup pg : entry.getValue()) {
        pointCount += pg.count;
      }
      if (pointCount > result) {
        result = pointCount;
      }
    }

    return result;
  }

  private static final class Ratio {
    final int numerator;
    final int denumerator;

    public Ratio(int numerator, int denumerator) {
      final int gcd = gcd(numerator, denumerator);
      this.numerator = numerator / gcd;
      this.denumerator = denumerator / gcd;
    }

    public static Ratio fromInteger(int n) {
      return new Ratio(n, 1);
    }

    public Ratio mul(Ratio other) {
      return new Ratio(numerator * other.numerator,
          denumerator * other.denumerator);
    }

    public Ratio div(Ratio other) {
      return new Ratio(numerator * other.denumerator,
          denumerator * other.numerator);
    }

    public Ratio add(Ratio other) {
      return new Ratio(numerator * other.denumerator + other.numerator * denumerator,
          denumerator * other.denumerator);
    }

    public Ratio sub(Ratio other) {
      return new Ratio(numerator * other.denumerator - other.numerator * denumerator,
          denumerator * other.denumerator);
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof Ratio)) return false;
      Ratio ratio = (Ratio) o;
      return numerator == ratio.numerator &&
          denumerator == ratio.denumerator;
    }

    @Override
    public int hashCode() {
      return Objects.hash(numerator, denumerator);
    }

    @Override
    public String toString() {
      return "(" + numerator + "/" + denumerator + ")";
    }

    static int gcd(int a, int b) {
      while (b != 0) {
        int t = a;
        a = b;
        b = t % b;
      }
      return a;
    }
  }

  private interface Line {
  }

  // x = t
  private static final class VerticalLine implements Line {
    final Ratio t;

    public VerticalLine(Ratio t) {
      this.t = t;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof VerticalLine)) return false;
      VerticalLine that = (VerticalLine) o;
      return that.t.equals(t);
    }

    @Override
    public int hashCode() {
      return Objects.hash(t);
    }
  }

  // y = kx + t
  private static final class NonVerticalLine implements Line {
    final Ratio k;
    final Ratio t;

    NonVerticalLine(Ratio k, Ratio t) {
      this.k = k;
      this.t = t;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof NonVerticalLine)) return false;
      NonVerticalLine that = (NonVerticalLine) o;
      return Objects.equals(k, that.k) &&
          Objects.equals(t, that.t);
    }

    @Override
    public int hashCode() {
      return Objects.hash(k, t);
    }
  }

  // points, that duplicate each other
  private static final class PointGroup {
    final Ratio x;
    final Ratio y;
    final int count;

    public PointGroup(int x, int y, int count) {
      this.x = Ratio.fromInteger(x);
      this.y = Ratio.fromInteger(y);
      this.count = count;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof PointGroup)) return false;
      PointGroup that = (PointGroup) o;
      return count == that.count &&
          Objects.equals(x, that.x) &&
          Objects.equals(y, that.y);
    }

    @Override
    public int hashCode() {
      return Objects.hash(x, y, count);
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

  private static void printSolution(List<Point> points) {
    final String pointsStr = points.stream()
        .map(p -> "[" + p.x + ", " + p.y + "]")
        .collect(Collectors.toList()).toString();

    System.out.println("Input: " + pointsStr);
    System.out.println("Output: " + maxPoints(points.toArray(new Point[points.size()])));
  }

  public static final class MaxLinePointsCase1 {
    public static void main(String[] args) {
      printSolution(Arrays.asList(
          new Point(1, 1),
          new Point(2, 2),
          new Point(3, 3)
      ));
    }
  }

  public static final class MaxLinePointsCase2 {
    public static void main(String[] args) {
      printSolution(Arrays.asList(
          new Point(1, 1),
          new Point(3, 2),
          new Point(5, 3),
          new Point(4, 1),
          new Point(2, 3),
          new Point(1, 4)
      ));
    }
  }

  public static final class MaxLinePointsCase3 {
    public static void main(String[] args) {
      printSolution(Arrays.asList(//[[0,0],[94911151,94911150],[94911152,94911151]]
          new Point(0, 0),
          new Point(94911151, 94911150),
          new Point(94911152, 94911151)
      ));
    }
  }

  //
  // Implicit definition
  //

  private static final class Point {
    int x;
    int y;
    Point() { x = 0; y = 0; }
    Point(int a, int b) { x = a; y = b; }
  }
}
