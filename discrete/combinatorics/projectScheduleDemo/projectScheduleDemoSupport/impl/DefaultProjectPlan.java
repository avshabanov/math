package projectScheduleDemoSupport.impl;

import projectScheduleDemoSupport.*;

import java.util.*;

/**
 * TODO: resources
 *
 * @author Alexander Shabanov
 */
public final class DefaultProjectPlan implements ProjectPlan {

  private final Map<String, TaskImpl> taskMap = new HashMap<>();

  @Override
  public Task addTask(String taskName, long length, List<ResourceUnits> requiredResources, List<Task> dependentTasks) {
    if (taskMap.containsKey(taskName)) {
      throw new IllegalArgumentException("Duplicate task=" + taskName);
    }

    final TaskImpl task = new TaskImpl(taskName, length, requiredResources, dependentTasks);
    taskMap.put(taskName, task);

    return task;
  }

  @Override
  public Resource addResource(String resourceName, int unitCount) {
    throw new UnsupportedOperationException();
  }

  @Override
  public void clear() {
    taskMap.clear();
  }

  @Override
  public ProjectSchedule calculateSchedule() {
    final List<List<ProjectSchedule.ScheduledTask>> scheduledTasksOptions = new ArrayList<>(taskMap.size());

    findSchedule(0L,
        new ArrayList<>(taskMap.values()) /* tasks */,
        new ArrayList<>(taskMap.size()) /* scheduled tasks */,
        new ArrayList<>(taskMap.size()) /* completed tasks */,
        scheduledTasksOptions);

    if (scheduledTasksOptions.isEmpty()) {
      throw new RuntimeException("Schedule has not been found");
    }

    // TODO: find optimal (one or many?)

    return new ProjectScheduleImpl(scheduledTasksOptions.get(0));
  }

  //
  // Private
  //

  private static void findSchedule(long startTime,
                                   List<Task> tasks,
                                   List<ProjectSchedule.ScheduledTask> scheduledTasks,
                                   List<ProjectSchedule.ScheduledTask> completedTasks,
                                   List<List<ProjectSchedule.ScheduledTask>> scheduledTasksOptions) {
    // brute force lookup (no optimizations whatsoever)

    // [0] check if tasks array is empty - this identifies that schedule has been found
    if (tasks.isEmpty()) {
      final List<ProjectSchedule.ScheduledTask> result = new ArrayList<>(scheduledTasks.size() + completedTasks.size());
      result.addAll(completedTasks);
      result.addAll(scheduledTasks);
      scheduledTasksOptions.add(result);
      return;
    }

    // [1] find expired tasks
    final int completedTaskSize = completedTasks.size(); // remember completed tasks state to restore it later
    final Iterator<ProjectSchedule.ScheduledTask> scheduledTaskIterator = scheduledTasks.iterator();
    while (scheduledTaskIterator.hasNext()) {
      final ProjectSchedule.ScheduledTask scheduledTask = scheduledTaskIterator.next();
      final long completionTime = scheduledTask.getStartTime() + scheduledTask.getTask().getLength();
      if (completionTime <= startTime) {
        completedTasks.add(scheduledTask);
        scheduledTaskIterator.remove();
      }
    }

    // [2] iterate over all the available tasks
    final int scheduledTaskSize = scheduledTasks.size();
    for (int i = 0; i < tasks.size(); ++i) { // TODO: better task iteration
      final Task task = tasks.get(i);

      // TODO: take into an account resources...

      // check whether or not dependencies has been satisfied and task can be added to schedule
      // TODO: quick lookup for scheduled tasks
      boolean satisfied = true;
      for (final Task dep : task.getDependencies()) {
        boolean dependencyFound = false;
        for (final ProjectSchedule.ScheduledTask completedTask : completedTasks) {
          if (completedTask.is(dep)) {
            dependencyFound = true;
            break;
          }
        }

        if (!dependencyFound) {
          satisfied = false;
          break;
        }
      } // end dependency check

      if (!satisfied) {
        continue; // continue to the next task - this one can't be satisfied here
      }

      // make task unavailable
      tasks.remove(i);
      scheduledTasks.add(new ProjectScheduleImpl.ScheduledTaskImpl(task, startTime));
      --i;
    }

    // [3] recursively search for other tasks that can be scheduled in the next time spot
    // TODO: optimization - next time can be determined as tasks:min(task.getLength())
    findSchedule(startTime + 1, tasks, scheduledTasks, completedTasks, scheduledTasksOptions);

    // [4] restore tasks and scheduled tasks list
    while (scheduledTaskSize < scheduledTasks.size()) {
      final ProjectSchedule.ScheduledTask scheduledTask = scheduledTasks.remove(scheduledTaskSize);
      tasks.add(scheduledTask.getTask());
    }

    // [5] revert back scheduled and completed task lists
    while (completedTasks.size() > completedTaskSize) {
      scheduledTasks.add(completedTasks.remove(completedTaskSize));
    }
  }

  private static final class ProjectScheduleImpl implements ProjectSchedule {

    private final List<ScheduledTask> scheduledTasks;

    public ProjectScheduleImpl(List<ScheduledTask> scheduledTasks) {
      this.scheduledTasks = Collections.unmodifiableList(new ArrayList<>(scheduledTasks));
    }

    @Override
    public List<ScheduledTask> getScheduledTasks() {
      return scheduledTasks;
    }

    private static final class ScheduledTaskImpl implements ScheduledTask {
      private final Task task;
      private final long startTime;

      public ScheduledTaskImpl(Task task, long startTime) {
        this.task = task;
        this.startTime = startTime;
      }

      @Override
      public long getStartTime() {
        return startTime;
      }

      @Override
      public Task getTask() {
        return task;
      }

      @Override
      public String toString() {
        return "(" + getTask().getName() + ", start=" + getStartTime() + ", length=" + getTask().getLength() + ")";
      }
    }
  }

  private static abstract class AbstractNamed implements Named {
    private final String name;

    public AbstractNamed(String name) {
      this.name = Objects.requireNonNull(name, "name");
    }

    @Override
    public final String getName() {
      return name;
    }

    @Override
    public String toString() {
      return getClass().getSimpleName() + "#" + getName();
    }
  }

  private static final class TaskImpl extends AbstractNamed implements Task {
    final List<ResourceUnits> resources;
    final List<Task> dependencies;
    final long length;

    public TaskImpl(String name, long length, List<ResourceUnits> resources, List<Task> dependencies) {
      super(name);
      if (length <= 0) {
        throw new IllegalArgumentException("length can't be less than or equal to zero");
      }

      this.dependencies = Collections.unmodifiableList(new ArrayList<>(dependencies));
      this.resources = Collections.unmodifiableList(new ArrayList<>(resources));
      this.length = length;
    }

    @Override
    public List<Task> getDependencies() {
      return dependencies;
    }

    @Override
    public List<ResourceUnits> getRequiredResources() {
      return resources;
    }

    @Override
    public long getLength() {
      return length;
    }

    @Override
    public String toString() {
      return asReadableString();
    }
  }
}
