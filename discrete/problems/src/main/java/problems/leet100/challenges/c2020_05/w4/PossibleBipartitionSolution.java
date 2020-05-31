package problems.leet100.challenges.c2020_05.w4;

import java.util.*;
import java.util.stream.Collectors;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/537/week-4-may-22nd-may-28th/3342/
 *
 * <p>Given a set of N people (numbered 1, 2, ..., N), we would like to split everyone into two groups of any size.
 * Each person may dislike some other people, and they should not go into the same group.
 * Formally, if dislikes[i] = [a, b], it means it is not allowed to put the people numbered a and b into the same group.
 * Return true if and only if it is possible to split everyone into two groups in this way.</p>
 * <p>Note:
 * 1 <= N <= 2000
 * 0 <= dislikes.length <= 10000
 * 1 <= dislikes[i][j] <= N
 * dislikes[i][0] < dislikes[i][1]
 * There does not exist i != j for which dislikes[i] == dislikes[j].</p>
 */
public class PossibleBipartitionSolution {

  /*

  Input:
10
[[4,7],[4,8],[5,6],[1,6],[3,7],[2,5],[5,8],[1,2],[4,9],[6,10],[8,10],[3,6],[2,10],[9,10],[3,9],[2,3],[1,9],[4,6],[5,7],[3,8],[1,8],[1,7],[2,4]]
Output:
false
Expected:
true

   */

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(10, new int[][] {{4,7},{4,8},{5,6},{1,6},{3,7},{2,5},{5,8},{1,2},{4,9},
          {6,10},{8,10},{3,6},{2,10},{9,10},{3,9},{2,3},{1,9},{4,6},{5,7},{3,8},{1,8},{1,7},{2,4}});

      demo(5, new int[][] {{1, 2}, {3,4}, {4,5}, {3,5}});
      demo(5, new int[][] {{1, 2}, {2,3}, {3,4}, {4,5}, {1,5}});
      demo(4, new int[][] {{1, 2}, {1,3}, {2,4}});
      demo(3, new int[][] {{1, 2}, {1,3}, {2,3}});

    }
  }

  private static void demo(int n, int[][] partitionPairs) {
    final boolean result = possibleBipartition(n, partitionPairs);
    System.out.printf(
        "Input: %d, [%s]\nOutput: %s\n",
        n, Arrays.stream(partitionPairs).map(Arrays::toString).collect(Collectors.joining(", ")),
        result
    );
  }

  private static boolean possibleBipartition(int n, int[][] partitionPairs) {
    final AdjacencyMap m = new AdjacencyMap(partitionPairs);
    final Map<Integer, Boolean> colors = new HashMap<>();
    for (final Integer node : m.map.keySet()) {
      if (colors.containsKey(node) || m.isBipartiteGraph(node, true, colors)) {
        continue;
      }
      return false;
    }
    return true;
  }

  private static final class AdjacencyMap {
    final Map<Integer, Set<Integer>> map = new HashMap<>();

    AdjacencyMap(int[][] partitionPairs) {
      for (int[] pair : partitionPairs) {
        if (pair[0] == pair[1]) {
          throw new IllegalArgumentException("left==right for pair=" + Arrays.toString(pair));
        }

        final Integer left = pair[0];
        final Integer right = pair[1];

        final Set<Integer> leftOpp = map.computeIfAbsent(left, k -> new HashSet<>());
        final Set<Integer> rightOpp = map.computeIfAbsent(right, k -> new HashSet<>());

        leftOpp.add(right);
        rightOpp.add(left);
      }
    }

    boolean isBipartiteGraph(Integer node, boolean isWhite, Map<Integer, Boolean> colors) {
      final Boolean existingColor = colors.get(node);
      if (existingColor != null) {
        return existingColor == isWhite;
      }

      colors.put(node, isWhite);

      boolean result = true;
      for (final Integer vertex : map.get(node)) {
        if (!isBipartiteGraph(vertex, !isWhite, colors)) {
          result = false;
        }
      }
      return result;
    }
  }

  //
  // Published Solution
  //

  /**
   * <p>Approach 1: Depth-First Search
   * Intuition
   *
   * It's natural to try to assign everyone to a group.
   * Let's say people in the first group are red, and people in the second group are blue.
   *
   * If the first person is red, anyone disliked by this person must be blue.
   * Then, anyone disliked by a blue person is red, then anyone disliked by a red person is blue, and so on.
   *
   * If at any point there is a conflict, the task is impossible, as every step logically follows from the first step.
   * If there isn't a conflict, then the coloring was valid, so the answer would be true.
   *
   * Algorithm
   *
   * Consider the graph on N people formed by the given "dislike" edges. We want to check that each connected component
   * of this graph is bipartite.
   *
   * For each connected component, we can check whether it is bipartite by just trying to coloring it with two colors.
   * How to do this is as follows: color any node red, then all of it's neighbors blue, then all of those neighbors red, and so on.
   * If we ever color a red node blue (or a blue node red), then we've reached a conflict.</p>
   * <p>Complexity Analysis
   * Time Complexity: O(N + E), where EE is the length of dislikes.
   * Space Complexity: O(N + E).</p>
   */
  private static final class Solution {
    ArrayList<Integer>[] graph;
    Map<Integer, Integer> color;

    public boolean possibleBipartition(int N, int[][] dislikes) {
      graph = new ArrayList[N+1];
      for (int i = 1; i <= N; ++i)
        graph[i] = new ArrayList();

      for (int[] edge: dislikes) {
        graph[edge[0]].add(edge[1]);
        graph[edge[1]].add(edge[0]);
      }

      color = new HashMap();
      for (int node = 1; node <= N; ++node)
        if (!color.containsKey(node) && !dfs(node, 0))
          return false;
      return true;
    }

    public boolean dfs(int node, int c) {
      if (color.containsKey(node))
        return color.get(node) == c;
      color.put(node, c);

      for (int nei: graph[node])
        if (!dfs(nei, c ^ 1))
          return false;
      return true;
    }
  }
}
