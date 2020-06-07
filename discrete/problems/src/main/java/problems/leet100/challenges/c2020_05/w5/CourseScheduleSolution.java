package problems.leet100.challenges.c2020_05.w5;

import java.util.*;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/538/week-5-may-29th-may-31st/3344/
 * <p>There are a total of numCourses courses you have to take, labeled from 0 to numCourses-1.
 * Some courses may have prerequisites, for example to take course 0 you have to first take course 1,
 * which is expressed as a pair: [0,1]
 * Given the total number of courses and a list of prerequisite pairs, is it possible for you to finish all courses?</p>
 * <p>Constraints:
 * The input prerequisites is a graph represented by a list of edges, not adjacency matrices. Read more about how a graph is represented.
 * You may assume that there are no duplicate edges in the input prerequisites.
 * 1 <= numCourses <= 10^5</p>
 */
public class CourseScheduleSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println(canFinish(3, new int[][] {{0,1}, {0,2}, {1,2}}));
      System.out.println(canFinish(2, new int[][] {{1,0}}));
      System.out.println(canFinish(2, new int[][] {{1,0}, {0,1}}));
    }
  }

  private static boolean canFinish(int numCourses, int[][] prerequisites) {
    final Graph g = new Graph(prerequisites);
    final Set<Integer> analyzed = new HashSet<>();
    final Set<Integer> visited = new HashSet<>();
    for (final Integer v : g.vertices.keySet()) {
      if (analyzed.contains(v)) {
        continue;
      }
      if (g.hasLoops(v, visited, analyzed)) {
        return false;
      }
    }
    return true;
  }

  private static final class Graph {
    private final Map<Integer, Set<Integer>> vertices = new HashMap<>();

    private void addPair(int from, int to) {
      vertices.compute(from, (k, v) -> {
        if (v == null) {
          v = new HashSet<>();
        }
        v.add(to);
        return v;
      });
    }

    Graph(int[][] prerequisites) {
      for (int[] p : prerequisites) {
        addPair(p[0], p[1]);
      }
    }

    boolean hasLoops(Integer vertex, Set<Integer> visited, Set<Integer> analyzed) {
      if (visited.contains(vertex)) {
        return true;
      }
      visited.add(vertex);
      analyzed.add(vertex);

      for (final Integer v : vertices.getOrDefault(vertex, Collections.emptySet())) {
        if (hasLoops(v, visited, analyzed)) {
          return true;
        }
      }

      visited.remove(vertex);
      return false;
    }
  }
}
