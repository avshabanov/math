import java.util.*;

/**
 * @author Alexander Shabanov
 */
public class ProjectScheduleDemo {

  public static void main(String[] args) {
    demo1(new DefaultProjectPlan());
  }

  private static void demo1(ProjectPlan plan) {
    final Task t1 = plan.add("t1", 1, Collections.emptyList(), Collections.emptyList());
    final Task t2 = plan.add("t2", 1, Collections.emptyList(), Collections.singletonList(t1));
    plan.add("t3", 1, Collections.emptyList(), Collections.singletonList(t2));
  }

  //
  // Private
  //

  private interface Named {
    String getName();
  }

  private interface Task extends Named {
  }

  private interface Resource extends Named {
    int getUnitCount();
  }

  private interface ProjectPlan {
    Task add(String taskName, int length, List<Resource> requiredResources, List<Task> dependentTasks);
  }

  //
  // Private - Impl
  //

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

  private static final class DefaultProjectPlan implements ProjectPlan {
    private final Map<String, TaskTuple> taskMap = new HashMap<>();

    @Override
    public Task add(String taskName, int length, List<Resource> requiredResources, List<Task> dependentTasks) {
      return null;
    }

    //
    // Private
    //

    private static final class TaskTuple {
      final TaskImpl task;
      final List<Resource> resources;
      final List<Task> dependencies;

      public TaskTuple(TaskImpl task, List<Resource> resources, List<Task> dependencies) {
        this.task = task;
        this.resources = resources;
        this.dependencies = dependencies;
      }
    }
  }

  private static final class TaskImpl extends AbstractNamed implements Task {

    public TaskImpl(String name) {
      super(name);
    }
  }
}
