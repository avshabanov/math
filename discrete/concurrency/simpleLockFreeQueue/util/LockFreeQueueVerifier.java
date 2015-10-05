package util;

import java.util.Arrays;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * @author Alexander Shabanov
 */
public final class LockFreeQueueVerifier {
  private final int numThreads;
  private final Queue<Integer> queue;

  public LockFreeQueueVerifier(int numThreads, Queue<Integer> queue) {
    this.numThreads = numThreads;
    this.queue = queue;
  }

  public void start() {
    addElementsToStackAndVerify();
    removeElementsFromQueueAndVerify();
  }

  //
  // Private
  //

  private void addElementsToStackAndVerify() {
    final CountDownLatch startGate = new CountDownLatch(1);
    final CountDownLatch stopGate = new CountDownLatch(numThreads);

    for (int i = 0; i < numThreads; ++i) {
      final Integer num = i; // make boxed version to avoid extra boxing costs
      final Thread thread = new Thread(() -> {
        try {
          startGate.await();
          queue.add(num);
          stopGate.countDown(); // signal that operation has been completed
        } catch (InterruptedException e) {
          System.err.println("Unexpected interruption of push thread #" + num);
          Thread.currentThread().interrupt();
        }
      });

      thread.start();
    }

    // signal that all threads can start modifying queue simultaneously
    long delta = System.nanoTime();
    startGate.countDown();
    // now wait until all thread finish processing
    try {
      stopGate.await();
      delta = System.nanoTime() - delta;
    } catch (InterruptedException e) {
      System.err.println("Unexpected interruption");
    }

    System.out.print("dTime: " + delta + "ns ");

    // then verify the queue
    final List<Integer> elements = Arrays.asList(queue.toArray(new Integer[queue.size()]));
    if (elements.size() == numThreads) {
      System.out.println("[PASSED] Queue contains the same amount of elements that have been passed");
    } else {
      System.out.println("[FAILED] Queue contains different amount of elements that have been passed, actual=" +
          elements.size() + ", expected=" + numThreads);
    }
  }



  private void removeElementsFromQueueAndVerify() {
    final int numElements = queue.size();
    final CountDownLatch startGate = new CountDownLatch(1);
    final CountDownLatch stopGate = new CountDownLatch(numElements);
    final AtomicInteger popFailures = new AtomicInteger(0);

    for (int i = 0; i < numElements; ++i) {
      final int threadIndex = i;
      final Thread thread = new Thread(() -> {
        try {
          startGate.await();
          final Integer result = queue.remove();
          if (result == null) {
            popFailures.incrementAndGet();
          }
          stopGate.countDown(); // signal that operation has been completed
        } catch (InterruptedException e) {
          System.err.println("Unexpected interruption of pop thread #" + threadIndex);
          Thread.currentThread().interrupt();
        }
      });

      thread.start();
    }

    // signal that all threads can start modifying queue simultaneously
    long delta = System.nanoTime();
    startGate.countDown();
    // now wait until all thread finish processing
    try {
      stopGate.await();
      delta = System.nanoTime() - delta;
    } catch (InterruptedException e) {
      System.err.println("Unexpected interruption");
    }

    System.out.print("dTime: " + delta + "ns ");

    // then verify the queue
    final List<Integer> elements = Arrays.asList(queue.toArray(new Integer[queue.size()]));
    if (elements.size() == 0) {
      System.out.println("[PASSED] Queue is now empty");
    } else {
      System.out.println("[FAILED] Queue is not empty, size=" + elements.size() +
          ", countOfPopFailures=" + popFailures.get());
    }
  }
}
