package problems.leet100.challenges.cmisc;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Task Scheduler
 * You are given a char array representing tasks CPU need to do.
 * It contains capital letters A to Z where each letter represents a different task.
 * Tasks could be done without the original order of the array.
 * Each task is done in one unit of time.
 * For each unit of time, the CPU could complete either one task or just be idle.
 * However, there is a non-negative integer n that represents the cooldown period between two same tasks
 * (the same letter in the array), that is that there must be at least n units of time between any two same tasks.
 * You need to return the least number of units of times that the CPU will take to finish all the given tasks.
 */
public class TaskScheduler {

  public static final class Demo {
    public static void main(String[] args) {
      System.out.println("01 -> " + leastInterval("bacaba".toCharArray(), 1));
      System.out.println("02 -> " + leastInterval("aaabbb".toCharArray(), 2));
      System.out.println("03 -> " + leastInterval("aaabbb".toCharArray(), 0));
      System.out.println("04 -> " + leastInterval("aaaaaabcdefg".toCharArray(), 2));
    }
  }

  private static int leastInterval(char[] tasks, int n) {
    final Map<Character, Integer> frequences = new HashMap<>(50);
    for (final char ch : tasks) {
      frequences.compute(ch, (k, v) -> 1 + (v == null ? 0 : v));
    }

    final TreeSet<TaskEntry> entries = frequences.entrySet().stream()
        .map(e -> new TaskEntry(e.getKey(), e.getValue(), -n)).collect(Collectors.toCollection(TreeSet::new));
    final Queue<TaskEntry> entryQueue = new ArrayDeque<>();

    int step = 0;
    for (; !(entryQueue.isEmpty() && entries.isEmpty()); ++step) {
      // add elements that could be reused again
      while (!entryQueue.isEmpty()) {
        if ((step - entryQueue.peek().lastIndex) > n) {
          entries.add(entryQueue.poll());
        } else {
          break;
        }
      }

      if (entries.isEmpty()) {
        continue;
      }

      final TaskEntry candidate = Objects.requireNonNull(entries.pollFirst());
      candidate.lastIndex = step;
      candidate.counter--;
      if (candidate.counter > 0) {
        entryQueue.add(candidate);
      }
    }

    return step;
  }

  private static final class TaskEntry implements Comparable<TaskEntry> {
    private final char ch;
    private int counter;
    private int lastIndex;

    TaskEntry(char ch, int counter, int lastIndex) {
      this.ch = ch;
      this.counter = counter;
      this.lastIndex = lastIndex;
    }

    @Override public int compareTo(TaskEntry o) {
      final int n = Integer.compare(o.counter, counter);
      return n != 0 ? n : Character.compare(o.ch, ch);
    }
  }
}
