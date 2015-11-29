package projectScheduleDemoSupport;

import java.util.List;

/**
 * @author Alexander Shabanov
 */
public interface ProjectPlan {

  Task addTask(String taskName, long length, List<ResourceUnits> requiredResources, List<Task> dependentTasks);

  Resource addResource(String resourceName, int unitCount);

  void clear();

  ProjectSchedule calculateSchedule();
}
