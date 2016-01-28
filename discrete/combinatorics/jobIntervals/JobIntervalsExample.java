import java.util.*;

/**
 * Sample run:
 * <pre>
 * ---
 * Given schedule=[]
 * Intervals=[]
 * ---
 * Given schedule=[JobEntry{name='A', from=0, to=5}]
 * Intervals=[JobsInterval{jobs=[A], from=0, to=5}]
 * ---
 * Given schedule=[JobEntry{name='A', from=0, to=5}, JobEntry{name='B', from=1, to=7}]
 * Intervals=[JobsInterval{jobs=[A], from=0, to=1}, JobsInterval{jobs=[A, B], from=1, to=5}, JobsInterval{jobs=[B], from=5, to=7}]
 * ---
 * Given schedule=[JobEntry{name='A', from=0, to=5}, JobEntry{name='B', from=1, to=2}]
 * Intervals=[JobsInterval{jobs=[A], from=0, to=1}, JobsInterval{jobs=[A, B], from=1, to=2}, JobsInterval{jobs=[A], from=2, to=5}]
 * ---
 * Given schedule=[JobEntry{name='A', from=0, to=5}, JobEntry{name='B', from=1, to=4}, JobEntry{name='C', from=3, to=7}, JobEntry{name='D', from=6, to=8}, JobEntry{name='A', from=10, to=12}]
 * Intervals=[JobsInterval{jobs=[A], from=0, to=1}, JobsInterval{jobs=[A, B], from=1, to=3}, JobsInterval{jobs=[A, B, C], from=3, to=4}, JobsInterval{jobs=[A, C], from=4, to=5}, JobsInterval{jobs=[C], from=5, to=6}, JobsInterval{jobs=[C, D], from=6, to=7}, JobsInterval{jobs=[D], from=7, to=8}, JobsInterval{jobs=[A], from=10, to=12}]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class JobIntervalsExample {

  public static void main(String[] args) {
    demo(Collections.emptyList());
    demo(Collections.singletonList(e("A", 0, 5)));
    demo(Arrays.asList(e("A", 0, 5), e("B", 1, 7)));
    demo(Arrays.asList(e("A", 0, 5), e("B", 1, 2)));
    demo(Arrays.asList(e("A", 0, 5), e("B", 1, 4), e("C", 3, 7), e("D", 6, 8), e("A", 10, 12)));
  }

  public static void demo(List<JobEntry> entries) {
    System.out.println("---\nGiven schedule=" + entries +
        "\nIntervals=" + toIntervals(Collections.unmodifiableList(entries)));
  }

  public static JobEntry e(String name, int from, int to) {
    return new JobEntry(name, from, to);
  }

  public static final class JobEntry {
    private final String name;
    private final int from;
    private final int to;

    public JobEntry(String name, int from, int to) {
      this.name = name;
      this.from = from;
      this.to = to;
    }

    @Override
    public String toString() {
      return "JobEntry{" +
          "name='" + name + '\'' +
          ", from=" + from +
          ", to=" + to +
          '}';
    }
  }

  public static final class JobsInterval {
    private final List<String> jobs;
    private final int from;
    private final int to;

    public JobsInterval(List<String> jobs, int from, int to) {
      this.jobs = jobs;
      this.from = from;
      this.to = to;
    }

    @Override
    public String toString() {
      return "JobsInterval{" +
          "jobs=" + jobs +
          ", from=" + from +
          ", to=" + to +
          '}';
    }
  }

  public static List<JobsInterval> toIntervals(List<JobEntry> schedule) {
    final List<JobEntry> sortedEntries = new ArrayList<>(schedule);
    Collections.sort(sortedEntries, (o1, o2) -> o1.from - o2.from);

    final int scheduleSize = sortedEntries.size();
    final List<JobsInterval> result = new ArrayList<>(scheduleSize);
    int currentTime = 0;

    int taskIndex = 0;
    // iterate over tasks
    for (; taskIndex < scheduleSize;) {
      int nextTime = Integer.MAX_VALUE;
      boolean foundTaskWithin = false;
      final List<String> tasks = new ArrayList<>();
      for (int j = taskIndex; j < scheduleSize; ++j) {
        final JobEntry entry = sortedEntries.get(j);
        if (entry.to <= currentTime) {
          if (!foundTaskWithin) {
            ++taskIndex;
          }
          continue;
        }

        if (entry.from <= currentTime) {
          nextTime = Math.min(nextTime, entry.to);
          tasks.add(entry.name);
          foundTaskWithin = true;
        } else {
          nextTime = Math.min(nextTime, entry.from);
          break;
        }
      }

      // add found interval
      if (tasks.size() > 0) {
        result.add(new JobsInterval(tasks, currentTime, nextTime));
        currentTime = nextTime;
      }

      // set next schedule time
      if (!foundTaskWithin) {
        if (taskIndex < scheduleSize) {
          currentTime = sortedEntries.get(taskIndex).from;
        }
      }
    }

    return result;
  }
}
