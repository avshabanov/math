import java.util.*;

/**
 * @author Alexander Shabanov
 */
public class TaskSequenceExample {

  public static void main(String[] args) {
    final List<Task> tasks = new ArrayList<>();
    tasks.add(new Task("A"));
    tasks.add(new Task("B"));
    tasks.add(new Task("C"));
    tasks.add(new Task("D"));
    tasks.get(2).addDependency(tasks.get(0));
    tasks.get(1).addDependency(tasks.get(2));
    tasks.get(3).addDependency(tasks.get(1));
    demo(tasks);

  }


  public static void demo(List<Task> tasks) {
    System.out.println("Given tasks=" + tasks + " execution order=" + getExecutionOrder(tasks));
  }

  //
  // Generator
  //

  private static List<Task> getExecutionOrder(List<Task> tasks) {
    final List<Task> result = new ArrayList<>(tasks.size());
    //final Set<Task> candidates = new HashSet<>(); TODO: optimize

    // fill parent tasks
    final Map<Task, Set<Task>> parentTasks = new HashMap<>();
    for (final Task task : tasks) {
      if (task.getDependencies().isEmpty()) {
        //candidates.add(task); TODO: optimize
        parentTasks.put(task, Collections.emptySet());
        continue;
      }
      parentTasks.put(task, new HashSet<>(task.getDependencies()));
    }

    // brain dead for loop - should be used for comparing optimized solution with non-optimized one

    for (;;) {
      if (parentTasks.isEmpty()) {
        break;
      }

      boolean removed = false;
      for (final Iterator<Map.Entry<Task, Set<Task>>> it = parentTasks.entrySet().iterator(); it.hasNext();) {
        final Map.Entry<Task, Set<Task>> entry = it.next();
        if (entry.getValue().isEmpty()) {
          result.add(entry.getKey());
          it.remove();
          removed = true;

          // clean up dependencies
          for (final Set<Task> value : parentTasks.values()) {
            if (!value.isEmpty()) {
              value.remove(entry.getKey());
            }
          }
        }
      }

      if (!removed) {
        throw new RuntimeException("Given list of tasks contains loops: " + tasks);
      }
    }

    // TODO: optimize
//    final List<Task> nextCandidates = new ArrayList<>();
//    for (;;) {
//      boolean nextTaskFound = false;
//
//      nextCandidates.clear();
//      for (Iterator<Task> it = candidates.iterator(); it.hasNext(); ) {
//        final Task task = it.next();
//
//        final Set<Task> parents = parentTasks.get(task);
//        if (parents == null || parents.isEmpty()) {
//          result.add(task);
//          for (final Task dependency : task.getDependencies()) {
//            final Set<Task> depParentTask = parentTasks.get(dependency);
//            depParentTask.remove(task); // remove this task from parent entries
//            nextCandidates.add(dependency);
//          }
//          it.remove();
//          nextTaskFound = true;
//        }
//      }
//      candidates.addAll(nextCandidates);
//
//      if (!nextTaskFound) {
//        if (parentTasks.isEmpty()) {
//          break;
//        }
//
//        throw new RuntimeException("Given list of tasks contains loops: " + tasks);
//      }
//    }

    return result;
  }


  //
  // Task definition
  //

  private static final class Task {
    private final String name;
    private final Set<Task> dependencies = new HashSet<>();

    public Task(String name) {
      this.name = name;
    }

    public String getName() {
      return name;
    }

    public void addDependency(Task other) {
      this.dependencies.add(other);
    }

    public Set<Task> getDependencies() {
      return dependencies;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof Task)) return false;

      Task task = (Task) o;

      if (name != null ? !name.equals(task.name) : task.name != null) return false;
      return !(dependencies != null ? !dependencies.equals(task.dependencies) : task.dependencies != null);

    }

    @Override
    public int hashCode() {
      int result = name != null ? name.hashCode() : 0;
      result = 31 * result + (dependencies != null ? dependencies.hashCode() : 0);
      return result;
    }

    @Override
    public String toString() {
      return getName();
    }
  }

}
