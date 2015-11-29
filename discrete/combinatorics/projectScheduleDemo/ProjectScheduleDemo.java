import projectScheduleDemoSupport.*;
import projectScheduleDemoSupport.impl.DefaultProjectPlan;

import java.util.*;

/**
 * Sample output (demo1):
 *
 * <pre>
 * # Demo1
 * Tasks:
 * t1: length=1
 * t2: length=1, dependsOn=[t1]
 * t3: length=1, dependsOn=[t2]
 * ===
 * Gant diagram, criticalPathTime=3
 *  0 X.. (t1, start=0, length=1)
 *  1 .X. (t2, start=1, length=1)
 *  2 ..X (t3, start=2, length=1)
 * ----
 *
 *
 * # Demo2
 * Tasks:
 * t1: length=1
 * t2: length=2, dependsOn=[t1]
 * t3: length=3, dependsOn=[t1]
 * t4: length=5
 * t5: length=2, dependsOn=[t2]
 * t6: length=4, dependsOn=[t3]
 * t7: length=2, dependsOn=[t2, t4]
 * ===
 * Gant diagram, criticalPathTime=8
 *  0 X....... (t1, start=0, length=1)
 *  1 XXXXX... (t4, start=0, length=5)
 *  2 .XX..... (t2, start=1, length=2)
 *  3 .XXX.... (t3, start=1, length=3)
 *  4 ...XX... (t5, start=3, length=2)
 *  5 ....XXXX (t6, start=4, length=4)
 *  6 .....XX. (t7, start=5, length=2)
 * ----
 * </pre>
 *
 * @author Alexander Shabanov
 */
public class ProjectScheduleDemo {

  public static void main(String[] args) {
    demo1(new DefaultProjectPlan());
    demo2(new DefaultProjectPlan());
  }

  private static void demo1(ProjectPlan plan) {
    System.out.println("\n# Demo1");

    final Task t1 = plan.addTask("t1", 1, Collections.emptyList(), Collections.emptyList());
    final Task t2 = plan.addTask("t2", 1, Collections.emptyList(), Collections.singletonList(t1));
    final Task t3 = plan.addTask("t3", 1, Collections.emptyList(), Collections.singletonList(t2));

    System.out.println("Tasks:");
    for (final Task t : Arrays.asList(t1, t2, t3)) {
      System.out.println(t.asReadableString());
    }
    System.out.println("===");

    final ProjectSchedule schedule = plan.calculateSchedule();
    System.out.println(schedule.asGantString());
  }


  private static void demo2(ProjectPlan plan) {
    System.out.println("\n# Demo2");

    final Task t1 = plan.addTask("t1", 1, Collections.emptyList(), Collections.emptyList());
    final Task t2 = plan.addTask("t2", 2, Collections.emptyList(), Collections.singletonList(t1));
    final Task t3 = plan.addTask("t3", 3, Collections.emptyList(), Collections.singletonList(t1));
    final Task t4 = plan.addTask("t4", 5, Collections.emptyList(), Collections.emptyList());
    final Task t5 = plan.addTask("t5", 2, Collections.emptyList(), Collections.singletonList(t2));
    final Task t6 = plan.addTask("t6", 4, Collections.emptyList(), Collections.singletonList(t3));
    final Task t7 = plan.addTask("t7", 2, Collections.emptyList(), Arrays.asList(t2, t4));

    System.out.println("Tasks:");
    for (final Task t : Arrays.asList(t1, t2, t3, t4, t5, t6, t7)) {
      System.out.println(t.asReadableString());
    }
    System.out.println("===");

    final ProjectSchedule schedule = plan.calculateSchedule();
    System.out.println(schedule.asGantString());
  }
}

