/**
 * Prints numbers from 0 to N in proper order using threads.
 *
 * @author Alexander Shabanov
 */
public class ConsecutiveThreadExecution {

  public static void main(String[] args) {
    printNumbers(20);
  }

  private static void printNumbers(int n) {
    final Object[] monitors = new Object[n + 1];
    for (int i = 0; i < monitors.length; ++i) {
      monitors[i] = new Object();
    }

    final String[] data = new String[n];
    for (int i = 0; i < n; ++i) {
      data[i] = "Number " + i;
    }

    for (int i = 0; i < n; ++i) {
      final int current = i;
      final Thread thread = new Thread(new Runnable() {
        @Override
        public void run() {
          try {
            synchronized (monitors[current]) {
              monitors[current].wait();
            }
          } catch (InterruptedException e) {
            System.err.println("ERROR: Spurious wakeup?");
            // TODO: CountDownLatch or the like is probably more preferred over monitors here, see also JDK docs:
            //          A thread can also wake up without being notified, interrupted, or
            //          timing out, a so-called <i>spurious wakeup</i>.  While this will rarely
            //          occur in practice, applications must guard against it by testing for
            //          the condition that should have caused the thread to be awakened, and
            //          continuing to wait if the condition is not satisfied.
            Thread.currentThread().interrupt(); // TODO: Incomplete, protection from spurious wakeups is required!
          }

          System.out.println("Data: " + data[current]);

          // notify next
          final int nextIndex = current + 1;
          synchronized (monitors[nextIndex]) {
            monitors[nextIndex].notify();
          }

          System.out.println("Thread " + current + " finishes");
        }
      });

      thread.start();
    }

    // notify first thread
    synchronized (monitors[0]) {
      monitors[0].notify();
    }

    // wait until last thread completes
    // TODO: again, protection from spurious wakeups is required, see TODO above
    try {
      synchronized (monitors[n]) {
        monitors[n].wait();
      }
      System.out.println("DONE");
    } catch (InterruptedException e) {
      System.err.println("ERROR: Spurious wakeup?");
      Thread.currentThread().interrupt();
    }
  }
}
