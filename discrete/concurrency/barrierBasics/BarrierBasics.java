import java.util.concurrent.BrokenBarrierException;
import java.util.concurrent.CyclicBarrier;

/**
 * Reworked example to 'Java Concurrency in Practice' - 5.5.4. Barriers
 *
 * The output looks as follows:
 *
 * <code>
 * Time: 2 - TASK_1 starts
 * Time: 2 - TASK_0 starts
 * Time: 3 - TASK_2 starts
 * Time: 3 - TASK_3 starts
 * Time: 404 - barrier action
 * Time: 404 - TASK_3 starts
 * Time: 404 - TASK_0 starts
 * Time: 404 - TASK_1 starts
 * Time: 404 - TASK_2 starts
 * Time: 805 - barrier action
 * </code>
 *
 * @author Alexander Shabanov
 */
public class BarrierBasics {
  private static final int WORKER_COUNT = 4;

  private final long startTime = System.currentTimeMillis();

  public static void main(String[] args) {
    new BarrierBasics().start();
  }

  public void start() {
    final CyclicBarrier barrier = new CyclicBarrier(WORKER_COUNT, new BarrierAction());
    for (int i = 0; i < WORKER_COUNT; ++i) {
      final String taskName = "TASK_" + i;
      final long delay = (i + 1) * 100L;
      final Thread thread = new Thread(new Runnable() {
        int runCount = 2;
        @Override
        public void run() {
          for (; runCount > 0; --runCount) {
            System.out.println("Time: " + (System.currentTimeMillis() - startTime) + " - " + taskName + " starts");

            try {
              Thread.sleep(delay);
              barrier.await();
            } catch (InterruptedException e) {
              System.err.println("Unexpected interruption of " + taskName);
              Thread.currentThread().interrupt();
              throw new IllegalStateException(e);
            } catch (BrokenBarrierException e) {
              System.err.println("Broken barrier in " + taskName);
              throw new IllegalStateException(e);
            }
          }
        }
      });

      thread.start();
    }
  }

  public final class BarrierAction implements Runnable {
    @Override
    public void run() {
      System.out.println("Time: " + (System.currentTimeMillis() - startTime) + " - barrier action");
    }
  }
}
