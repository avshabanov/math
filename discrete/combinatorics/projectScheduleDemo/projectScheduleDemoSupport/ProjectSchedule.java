package projectScheduleDemoSupport;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * TODO: include critical path
 *
 * @author Alexander Shabanov
 */
public interface ProjectSchedule {

  interface ScheduledTask {

    long getStartTime();

    Task getTask();

    default boolean is(Task other) {
      return getTask() == other;
    }
  }

  List<ScheduledTask> getScheduledTasks();

  default String asGantString() {
    final StringBuilder builder = new StringBuilder(200 * getScheduledTasks().size());

    final List<ScheduledTask> tasks = new ArrayList<>(getScheduledTasks());
    Collections.sort(tasks, (lhs, rhs) -> Long.compare(lhs.getStartTime(), rhs.getStartTime()));
    long criticalPathTime = 0;
    for (final ScheduledTask scheduledTask : tasks) {
      criticalPathTime = Math.max(criticalPathTime, scheduledTask.getStartTime() + scheduledTask.getTask().getLength());
    }

    builder.append("Gant diagram, criticalPathTime=").append(criticalPathTime).append('\n');
    for (int i = 0; i < tasks.size(); ++i) {
      builder.append(String.format("%2d ", i));
      final ScheduledTask task = tasks.get(i);
      long t = 0;
      for (long l = 0; l < task.getStartTime(); ++l) {
        builder.append('.');
        ++t;
      }
      for (long l = 0; l < task.getTask().getLength(); ++l) {
        builder.append('X');
        ++t;
      }
      for (; t < criticalPathTime; ++t) {
        builder.append('.');
      }
      builder.append(' ').append(task).append('\n');
    }
    builder.append("----\n");

    return builder.toString();
  }
}
