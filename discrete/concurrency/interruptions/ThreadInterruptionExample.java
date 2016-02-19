import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

/**
 * Demonstrates the importance of handling {@link InterruptedException}.
 *
 * Sample run:
 * <pre>
 * [Thread1] Wait #1..., isInterrupted=false
 * [Thread1] Wait #2..., isInterrupted=true
 * [Thread1] Execution completed. Total interruptions=2
 * [Thread2] Wait #1..., isInterrupted=false
 * [Thread2] Wait #2..., isInterrupted=false
 * [Thread2] Execution completed. Total interruptions=2
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class ThreadInterruptionExample {

  public static void main(String[] args) throws Exception {
    demoCorrectInterruptionHandling();
    demoIncorrectInterruptionHandling();
  }

  // Correct handling:

  private static void demoCorrectInterruptionHandling() throws Exception {
    final CountDownLatch gates[] = { new CountDownLatch(1), new CountDownLatch(1), new CountDownLatch(1) };

    final Thread thread = new Thread(() -> {
      try {
        gates[0].await();
      } catch (InterruptedException e) {
        Thread.currentThread().interrupt();
      }

      int interruptions = 0;

      try {
        System.out.println("[Thread1] Wait #1..., isInterrupted=" + Thread.currentThread().isInterrupted());
        Thread.sleep(500L);
      } catch (InterruptedException e) {
        Thread.currentThread().interrupt();
        ++interruptions;
      }

      gates[1].countDown();

      try {
        System.out.println("[Thread1] Wait #2..., isInterrupted=" + Thread.currentThread().isInterrupted());
        Thread.sleep(500L);
      } catch (InterruptedException e) {
        Thread.interrupted();
        ++interruptions;
      }

      gates[2].countDown();
      System.out.println("[Thread1] Execution completed. Total interruptions=" + interruptions);
    });

    thread.start();

    // start the thread
    gates[0].countDown();

    // wait for a while to ensure that thread starts sleeping
    Thread.sleep(100L);

    // interrupt the thread
    thread.interrupt();
    awaitOrDie(gates[1], "gate1");

    // wait for a while to ensure that thread starts sleeping again
    Thread.sleep(100L);

    // interrupt the thread
    thread.interrupt();

    // make sure execution completed
    awaitOrDie(gates[2], "gate2");
  }

  private static void awaitOrDie(CountDownLatch latch, String latchName) throws Exception {
    if (!latch.await(1L, TimeUnit.SECONDS)) {
      throw new AssertionError("Await failed for latch " + latchName);
    }
  }

  // Incorrect handling;

  private static void demoIncorrectInterruptionHandling() throws Exception {
    final CountDownLatch gates[] = { new CountDownLatch(1), new CountDownLatch(1), new CountDownLatch(1) };

    final Thread thread = new Thread(() -> {
      try {
        gates[0].await();
      } catch (InterruptedException e) {
        Thread.interrupted();
      }

      int interruptions = 0;

      try {
        System.out.println("[Thread2] Wait #1..., isInterrupted=" + Thread.currentThread().isInterrupted());
        Thread.sleep(500L);
      } catch (InterruptedException e) {
        // NOTE: interruption flag is not cleared here - (wrong!)
        ++interruptions;
      }

      gates[1].countDown();

      try {
        System.out.println("[Thread2] Wait #2..., isInterrupted=" + Thread.currentThread().isInterrupted());
        Thread.sleep(500L);
      } catch (InterruptedException e) {
        // NOTE: interruption flag is not cleared here - (wrong!)
        ++interruptions;
      }

      gates[2].countDown();
      System.out.println("[Thread2] Execution completed. Total interruptions=" + interruptions);
    });

    thread.start();

    // start the thread
    gates[0].countDown();

    // wait for a while to ensure that thread starts sleeping
    Thread.sleep(100L);

    // interrupt the thread
    thread.interrupt();
    awaitOrDie(gates[1], "gate1");

    // wait for a while to ensure that thread starts sleeping again
    Thread.sleep(100L);

    // interrupt the thread
    thread.interrupt();

    // make sure execution completed
    awaitOrDie(gates[2], "gate2");
  }
}
