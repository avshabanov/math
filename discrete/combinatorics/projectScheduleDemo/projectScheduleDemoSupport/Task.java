package projectScheduleDemoSupport;

import java.util.List;

/**
 * @author Alexander Shabanov
 */
public interface Task extends Named {

  List<Task> getDependencies();

  List<ResourceUnits> getRequiredResources();

  long getLength();

  default String asReadableString() {
    final StringBuilder builder = new StringBuilder(200);

    builder.append(getName()).append(": length=").append(getLength());

    if (!getRequiredResources().isEmpty()) {
      builder.append(", resources=[");
      boolean next = false;
      for (final ResourceUnits resourceUnit : getRequiredResources()) {
        if (next) {
          builder.append(", ");
        }
        next = true;
        builder.append(resourceUnit.getResource().getName()).append(" x ").append(resourceUnit.getUnits());
      }
      builder.append(']');
    }

    if (!getDependencies().isEmpty()) {
      builder.append(", dependsOn=[");
      boolean next = false;
      for (final Task task : getDependencies()) {
        if (next) {
          builder.append(", ");
        }
        next = true;
        builder.append(task.getName());
      }
      builder.append(']');
    }

    return builder.toString();
  }
}
