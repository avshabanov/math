import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * Example from 'Java Concurrency in Practice' - 5.5.1. Latches -
 * Using CountDownLatch for starting and stopping threads in timing tests.
 */
public final class LatchToStartAndStopThreads {

  public static void main(String[] args) {
    final AtomicInteger n = new AtomicInteger(0);

    runTimeTasks(3, new Runnable() {
      @Override
      public void run() {
        System.out.println("[Thread] n=" + n.incrementAndGet());
      }
    });
  }

  private static void runTimeTasks(int threadCount, final Runnable task) {
    final CountDownLatch startGate = new CountDownLatch(1);
    final CountDownLatch endGate = new CountDownLatch(threadCount);

    for (int i = 0; i < threadCount; ++i) {
      final Thread thread = new Thread(new Runnable() {
        @Override
        public void run() {
          try {
            startGate.await();
            task.run();
          } catch (InterruptedException ignored) {
            Thread.currentThread().interrupt(); // TODO: why is this important here?
          } finally {
            endGate.countDown();
          }
        }
      });

      thread.start();
    }

    final long start = System.nanoTime();
    startGate.countDown();
    try {
      endGate.await();
      final long end = System.nanoTime();
      System.out.println("All threads should be stopped now, time: " + (end - start) + " nanos");
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
    }
  }
}
