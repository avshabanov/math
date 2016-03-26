import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;

/**
 * Adapted example from 'Java Concurrency in Practice' - 5.5.2. FutureTask
 *
 * @author Alexander Shabanov
 */
public final class FutureTaskBasics {

  public static void main(String[] args) throws Exception {
    final long start = System.currentTimeMillis();

    final DeferredDataProvider provider = new DeferredDataProvider();
    Thread.sleep(1000L); // wait for one second
    final int data = provider.getDeferredData();

    final long end = System.currentTimeMillis();
    System.out.println("Result: data=" + data + ", timeDelta=" + (end - start) + " msec"); // should be ~2 seconds
  }

  //
  // Private
  //

  private static final class DeferredDataProvider {
    private final FutureTask<Integer> futureTask = new FutureTask<Integer>(() -> {
      Thread.sleep(2000L); // 2 sec delay, imitate long calculation...
      return 123;
    });

    public DeferredDataProvider() {
      final Thread thread = new Thread(futureTask);
      thread.start();
    }

    public int getDeferredData() {
      try {
        return futureTask.get();
      } catch (ExecutionException e) {
        final Throwable cause = e.getCause();
        if (cause instanceof RuntimeException) {
          throw (RuntimeException) cause;
        } else if (cause instanceof Error) {
          throw (Error) cause;
        }

        throw new RuntimeException("Unexpected checked exception", cause);
      } catch (InterruptedException e) {
        Thread.currentThread().interrupt();
        throw new IllegalStateException("Unexpected interruption", e);
      }
    }
  }
}
