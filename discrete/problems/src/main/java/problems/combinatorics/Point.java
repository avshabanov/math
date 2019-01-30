package problems.combinatorics;

import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Borrowed definition of the point class (defined by solution verifier).
 */
public final class Point {
  int x;
  int y;
  Point() { x = 0; y = 0; }
  Point(int a, int b) { x = a; y = b; }

  @Override
  public String toString() {
    return "{" + x + ", " + y + '}';
  }

  static void printSolution(List<Point> points, Function<Point[], Integer> maxPoints) {
    final String pointsStr = points.stream()
        .map(p -> "[" + p.x + ", " + p.y + "]")
        .collect(Collectors.toList()).toString();

    System.out.println("Input: " + pointsStr);
    System.out.println("Output: " + maxPoints.apply(points.toArray(new Point[points.size()])));
  }

  static List<Point> fromJsonArray(String json) {
    final ObjectMapper mapper = new ObjectMapper();
    try {
      final List<int[]> arr = mapper.readValue(json, new TypeReference<List<int[]>>(){});
      final List<Point> result = new ArrayList<>(arr.size());
      for (final int[] p : arr) {
        result.add(new Point(p[0], p[1]));
      }
      return result;
    } catch (IOException e) {
      throw new IllegalStateException(e);
    }
  }
}
