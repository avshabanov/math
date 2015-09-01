import java.util.concurrent.Semaphore;

/**
 * Reworked example to 'Java Concurrency in Practice' - 5.5.3. Semaphores
 *
 * The output looks as follows:
 *
 * <code>
 * Time: 1 - executing TASK_0 and waiting for 100 ms
 * End of task TASK_0
 * Time: 102 - executing TASK_1 and waiting for 200 ms
 * End of task TASK_1
 * Time: 303 - executing TASK_2 and waiting for 300 ms
 * End of task TASK_2
 * Time: 603 - executing TASK_3 and waiting for 400 ms
 * End of task TASK_3
 * Time: 1004 - executing TASK_4 and waiting for 500 ms
 * End of task TASK_4
 * </code>
 *
 * @author Alexander Shabanov
 */
public class SemaphoreBasics {
  private static final int TASK_COUNT = 5;
  private static final int SEMAPHORE_BOUND = 3;

  private final Semaphore semaphore;

  public static void main(String[] args) {
    new SemaphoreBasics().start();
  }

  public SemaphoreBasics() {
    this.semaphore = new Semaphore(SEMAPHORE_BOUND);
  }

  public void start() {
    final long start = System.currentTimeMillis();
    for (int i = 0; i < TASK_COUNT; ++i) {
      final Thread thread = new Thread(new Task("TASK_" + i, (i + 1) * 100, start));
      thread.run();
    }
  }

  public final class Task implements Runnable {

    private final String taskName;
    private final long delay;
    private final long startTime;

    public Task(String taskName, long delay, long startTime) {
      this.taskName = taskName;
      this.delay = delay;
      this.startTime = startTime;
    }

    @Override
    public void run() {
      try {
        semaphore.acquire(); // TODO: why is this always waiting for previous thread
        System.out.println("Time: " + (System.currentTimeMillis() - startTime) +
            " - executing " + taskName + " and waiting for " + delay + " ms");
        Thread.sleep(delay);
        System.out.println("End of task " + taskName);
        semaphore.release();
      } catch (InterruptedException e) {
        Thread.currentThread().interrupt();
        throw new IllegalStateException(e);
      }
    }
  }
}
