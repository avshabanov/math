package problems.leet100.challenges.c2020_06.w2;

import com.fasterxml.jackson.databind.ObjectMapper;

import java.io.File;
import java.io.IOException;
import java.util.*;

/**
 * https://leetcode.com/explore/featured/card/june-leetcoding-challenge/540/week-2-june-8th-june-14th/3360/
 * <p>There are n cities connected by m flights. Each flight starts from city u and arrives at v with a price w.
 *
 * Now given all the cities and flights, together with starting city src and the destination dst, your task is to
 * find the cheapest price from src to dst with up to k stops. If there is no such route, output -1.</p>
 * <p>Constraints:
 *
 * The number of nodes n will be in range [1, 100], with nodes labeled from 0 to n - 1.
 * The size of flights will be in range [0, n * (n - 1) / 2].
 * The format of each flight will be (src, dst, price).
 * The price of each flight will be in the range [1, 10000].
 * k is in the range of [0, n - 1].
 * There will not be any duplicated flights or self cycles.</p>
 */
public class CheapestFlightsWithinKStops {

  public static void main(String[] args) {
    demo(3, new int[][] {{0,1,100},{1,2,100},{0,2,500}}, 0, 2, 1);
    demo(3, new int[][] {{0,1,100},{1,2,100},{0,2,500}}, 0, 2, 0);
    demo(
        17,
        new int[][]{{0,12,28},{5,6,39},{8,6,59},{13,15,7},{13,12,38},{10,12,35},{15,3,23},{7,11,26},{9,4,65},{10,2,38},{4,7,7},{14,15,31},{2,12,44},{8,10,34},{13,6,29},{5,14,89},{11,16,13},{7,3,46},{10,15,19},{12,4,58},{13,16,11},{16,4,76},{2,0,12},{15,0,22},{16,12,13},{7,1,29},{7,14,100},{16,1,14},{9,6,74},{11,1,73},{2,11,60},{10,11,85},{2,5,49},{3,4,17},{4,9,77},{16,3,47},{15,6,78},{14,1,90},{10,5,95},{1,11,30},{11,0,37},{10,4,86},{0,8,57},{6,14,68},{16,8,3},{13,0,65},{2,13,6},{5,13,5},{8,11,31},{6,10,20},{6,2,33},{9,1,3},{14,9,58},{12,3,19},{11,2,74},{12,14,48},{16,11,100},{3,12,38},{12,13,77},{10,9,99},{15,13,98},{15,12,71},{1,4,28},{7,0,83},{3,5,100},{8,9,14},{15,11,57},{3,6,65},{1,3,45},{14,7,74},{2,10,39},{4,8,73},{13,5,77},{10,0,43},{12,9,92},{8,2,26},{1,7,7},{9,12,10},{13,11,64},{8,13,80},{6,12,74},{9,7,35},{0,15,48},{3,7,87},{16,9,42},{5,16,64},{4,5,65},{15,14,70},{12,0,13},{16,14,52},{3,10,80},{14,11,85},{15,2,77},{4,11,19},{2,7,49},{10,7,78},{14,6,84},{13,7,50},{11,6,75},{5,10,46},{13,8,43},{9,10,49},{7,12,64},{0,10,76},{5,9,77},{8,3,28},{11,9,28},{12,16,87},{12,6,24},{9,15,94},{5,7,77},{4,10,18},{7,2,11},{9,5,41}},
        13,
        4,
        13
    );
  }

  public static final class Demo2 {
    public static void main(String[] args) throws IOException {
      ObjectMapper m = new ObjectMapper();
      final int[][] flights = m.readValue(new File("/tmp/arr.json"), int[][].class);
      demo(
          94,
          flights,
          17,
          33,
          39
      );
    }
  }

  private static void demo(int n, int[][] flights, int src, int dst, int k) {
    long delta = System.currentTimeMillis();
    //final int p = OptimizedRecursionBasedSearch.findCheapestPrice(n, flights, src, dst, k);
    final int p = BreathScanSearch.findCheapestPrice(n, flights, src, dst, k);
    delta = System.currentTimeMillis() - delta;

    System.out.printf("[%d ms] n=%d, src=%d, dst=%d, k=%d; result price=%d\n", delta, n, src, dst, k, p);
  }

  private static final class BreathScanSearch {

    static int findCheapestPrice(int n, int[][] flights, int src, int dst, int K) {
      final List<Node> nodes = Node.toNodes(n, flights, K);

      // key part in this algorithm: the idea is to keep processing the node until we can find
      // either a smaller price for the same depth or smaller price for the same depth.
      final Deque<NodeDepthPrice> wavefront = new ArrayDeque<>();

      // special case: source node can be traveled to for zero price
      Arrays.fill(nodes.get(src).depthPrices, 0);

      // initial state of the algorithm: add all immediate neighbours of the source node
      for (final Edge e : nodes.get(src).edges) {
        nodes.get(e.target).depthPrices[0] = e.price;
        wavefront.add(new NodeDepthPrice(e.target, 0, e.price));
      }

      // next+ state of the algorithm: keep propagating the "wave" comprised of node-depth-price values
      // until we can find a slot that offers a smaller flight depth for the same or smaller price or a
      // smaller depth for the same or smaller price.
      while (!wavefront.isEmpty()) {
        final NodeDepthPrice ndp = wavefront.pop();
        final int nextDepth = ndp.depth + 1;
        if (nextDepth > K) {
          continue;
        }

        final Node source = nodes.get(ndp.node);
        for (final Edge edge : source.edges) {
          final Node target = nodes.get(edge.target);
          final int nextPrice = ndp.price + edge.price;

          // add next node IFF next price is smaller than any other found one on current depth or depth below
          boolean smallerPriceFound = false;
          for (int j = nextDepth; j >= 0; --j) {
            final int curPrice = target.depthPrices[j];
            if (curPrice <= nextPrice) {
              smallerPriceFound = true;
              break;
            }
          }

          if (smallerPriceFound) {
            // the node we're trying to insert has a smaller or same price on the smaller depth, no need to scan further
            continue;
          }

          // smaller price found, we need to find this element to the wavefront
          target.depthPrices[nextDepth] = nextPrice;

          wavefront.add(new NodeDepthPrice(edge.target, nextDepth, nextPrice));
        }
      }

      // finally find cheapest price within allowed depth
      int cheapestPrice = Integer.MAX_VALUE;
      for (int p : nodes.get(dst).depthPrices) {
        if (p < 0) {
          continue;
        }
        cheapestPrice = Math.min(cheapestPrice, p);
      }
      return cheapestPrice < Integer.MAX_VALUE ? cheapestPrice : -1;
    }

    private static final class NodeDepthPrice {
      final int node;
      final int depth;
      final int price;

      NodeDepthPrice(int node, int depth, int price) {
        this.node = node;
        this.depth = depth;
        this.price = price;
      }
    }

    private static final class Node {
      final List<Edge> edges = new ArrayList<>();
      final int[] depthPrices;

      Node(int k) {
        this.depthPrices = new int[k + 1];
        Arrays.fill(this.depthPrices, Integer.MAX_VALUE);
      }

      static List<Node> toNodes(int n, int[][] flights, int k) {
        List<Node> nodes = new ArrayList<>();
        for (int i = 0; i < n; ++i) {
          nodes.add(new Node(k));
        }
        for (int[] flight : flights) {
          nodes.get(flight[0]).edges.add(new Edge(flight[1], flight[2]));
        }
        return nodes;
      }
    }

    private static final class Edge {
      final int target;
      final int price;

      Edge(int target, int price) {
        this.target = target;
        this.price = price;
      }
    }
  }

  /**
   * Meets time limit exceeded for input #97 (number of nodes close to a hundred and number of
   * edges approaching max limit).
   */
  private static final class OptimizedRecursionBasedSearch {
    static int findCheapestPrice(int n, int[][] flights, int src, int dst, int K) {
      final Solver solver = new Solver(n, flights, dst, K);
      solver.find(new HashSet<>(), new Stats[n], src, -1);
      return solver.cheapestPrice;
    }

    private static final class Stats {
      int depth = Integer.MAX_VALUE;
      int price = Integer.MAX_VALUE;
    }

    private static final class Solver {
      private static final class Edge {
        final int target;
        final int weigth;

        Edge(int target, int weigth) {
          this.target = target;
          this.weigth = weigth;
        }
      }

      private final List<List<Edge>> edges = new ArrayList<>();
      private final int dst;
      private final int k;
      private int cheapestPrice = -1;
      private int priceSoFar = 0;

      public Solver(int n, int[][] flights, int dst, int k) {
        for (int i = 0; i < n; ++i) {
          edges.add(new ArrayList<>());
        }
        for (int[] flight : flights) {
          edges.get(flight[0]).add(new Edge(flight[1], flight[2]));
        }
        this.dst = dst;
        this.k = k;
      }

      void find(Set<Integer> visited, Stats[] stats, int node, int depth) {
        if (depth > k) {
          return;
        }

        if (node == dst) {
          cheapestPrice = cheapestPrice < 0 ? priceSoFar : Math.min(priceSoFar, cheapestPrice);
          return;
        }

        if (visited.contains(node)) {
          return;
        }

        Stats existingStats = stats[node];
        if (existingStats == null) {
          stats[node] = existingStats = new Stats();
        }
        if (existingStats.depth > depth || existingStats.price > priceSoFar) {
          existingStats.depth = depth;
          existingStats.price = priceSoFar;
        } else {
          return;
        }

        visited.add(node);
        final int nextDepth = depth + 1;
        for (final Edge edge : edges.get(node)) {
          priceSoFar += edge.weigth;
          find(visited, stats, edge.target, nextDepth);
          priceSoFar -= edge.weigth;
        }
        visited.remove(node);
      }
    }
  }
}
