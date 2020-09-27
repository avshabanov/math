package problems.leet100.challenges.cmisc;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Car Pooling
 * You are driving a vehicle that has capacity empty seats initially available for passengers.
 * The vehicle only drives east (ie. it cannot turn around and drive west.)
 *
 * Given a list of trips, trip[i] = [num_passengers, start_location, end_location] contains information about
 * the i-th trip: the number of passengers that must be picked up, and the locations to pick them up and drop them off.
 * The locations are given as the number of kilometers due east from your vehicle's initial location.
 *
 * Return true if and only if it is possible to pick up and drop off all passengers for all the given trips.
 *
 * Example 1:
 *
 * Input: trips = [[2,1,5],[3,3,7]], capacity = 4
 * Output: false
 * Example 2:
 *
 * Input: trips = [[2,1,5],[3,3,7]], capacity = 5
 * Output: true
 * Example 3:
 *
 * Input: trips = [[2,1,5],[3,5,7]], capacity = 3
 * Output: true
 * Example 4:
 *
 * Input: trips = [[3,2,7],[3,7,9],[8,3,9]], capacity = 11
 * Output: true
 *
 * Constraints:
 *
 * trips.length <= 1000
 * trips[i].length == 3
 * 1 <= trips[i][0] <= 100
 * 0 <= trips[i][1] < trips[i][2] <= 1000
 * 1 <= capacity <= 100000
 */
public class CarPooling {

  private static boolean carPooling(final int[][] trips, final int capacity) {
    Arrays.sort(trips, Comparator.comparingInt(l -> l[1]));
    final TreeMap<Integer, Integer> releaseCap = new TreeMap<>();
    int currentCapacity = capacity;
    final List<Integer> removalCandidates = new ArrayList<>();
    for (final int[] trip : trips) {
      final int numPassengers = trip[0];
      final int startLocation = trip[1];
      final int endLocation = trip[2];

      // first, release all capacity for previous end locations
      removalCandidates.clear();
      for (final Map.Entry<Integer, Integer> currentTrip : releaseCap.entrySet()) {
        if (currentTrip.getKey() > startLocation) {
          break;
        }
        removalCandidates.add(currentTrip.getKey());
        currentCapacity += currentTrip.getValue();
      }

      removalCandidates.forEach(releaseCap::remove);

      // finally, add current trip
      currentCapacity -= numPassengers;
      if (currentCapacity < 0) {
        return false;
      }

      releaseCap.compute(endLocation, (k, v) -> (v == null ? 0 : v) + numPassengers);
    }
    return true;
  }

  public static final class Demo1 {
    private static final class TestCase {
      final int[][] trips;
      final int capacity;
      final boolean expected;

      TestCase(int[][] trips, int capacity, boolean expected) {
        this.trips = trips;
        this.capacity = capacity;
        this.expected = expected;
      }
    }

    private static final TestCase[] TEST_CASES = {
        new TestCase(new int[][]{{7,5,6}, {6,7,8}, {10,1,6}}, 16, false),
        new TestCase(new int[][]{{2,1,5}, {3,5,7}}, 3, true),
        new TestCase(new int[][]{{2,1,5}, {3,3,7}}, 4, false),
        new TestCase(new int[][]{{3,2,7}, {3,7,9}, {8,3,9}}, 11, true)
    };

    public static void main(String[] args) {
      for (final TestCase tc : TEST_CASES) {
        final boolean actual = carPooling(tc.trips, tc.capacity);
        if (actual != tc.expected) {
          System.out.printf("actual=%b for trips=%s\n",
              actual,
              Arrays.stream(tc.trips).map(Arrays::toString).collect(Collectors.toList()));
        } else {
          System.out.println("[OK]");
        }

      }

    }
  }
}
