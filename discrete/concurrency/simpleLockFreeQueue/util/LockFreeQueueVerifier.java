package util;

import java.util.Arrays;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.CopyOnWriteArrayList;
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
    addRemoveElementsToQueue();
    addElementsToQueueAndVerify();
    removeElementsFromQueueAndVerify();
  }

  //
  // Private
  //

  private void addRemoveElementsToQueue() {
    final CountDownLatch startGate = new CountDownLatch(1);
    final CountDownLatch p0StopGate = new CountDownLatch(numThreads);

    final CountDownLatch p1Gate = new CountDownLatch(1);
    final CountDownLatch p1StopGate = new CountDownLatch(numThreads);

    final CountDownLatch p2Gate = new CountDownLatch(1);
    final CountDownLatch stopGate = new CountDownLatch(numThreads);

    final List<Integer> removedElements = new CopyOnWriteArrayList<>();

    for (int i = 0; i < numThreads; ++i) {
      final Integer num = i; // make boxed version to avoid extra boxing costs
      final Thread thread = new Thread(() -> {
        try {
          // P0: Even threads are adding, odd threads are doing nothing
          // this tests simultaneous add
          startGate.await();
          if (num % 2 == 0) {
            queue.add(num);
          }
          p0StopGate.countDown();

          // P1: Even threads are removing, odd threads are adding
          // this tests simultaneous add-remove
          p1Gate.await();
          Integer p1Removed = null;
          if (num % 2 == 0) {
            p1Removed = queue.remove();
          } else {
            queue.add(num);
          }
          p1StopGate.countDown();

          // P2: Even threads are doing nothing, odd threads are removing
          // this tests simultaneous remove
          p2Gate.await();
          Integer p2Removed = null;
          if (num % 2 != 0) {
            p2Removed = queue.remove();
          } else {
            Thread.sleep(1);
          }

          // add removed elements
          if (p1Removed != null) {
            removedElements.add(p1Removed);
          }
          if (p2Removed != null) {
            removedElements.add(p2Removed);
          }

          // signal that operation has been completed
          stopGate.countDown();
        } catch (InterruptedException e) {
          System.err.println("Unexpected interruption of push thread #" + num);
          Thread.currentThread().interrupt();
        }
      });

      thread.start();
    }

    // signal that all threads can start modifying queue simultaneously
    long delta = System.nanoTime();
    try {

      startGate.countDown();
      p0StopGate.await(); // P0 completion
      p1Gate.countDown();
      p1StopGate.await(); // P1 completion
      p2Gate.countDown();
      stopGate.await(); // P2 completion

      delta = System.nanoTime() - delta;
    } catch (InterruptedException e) {
      Thread.interrupted();
      throw new RuntimeException(e);
    }

    System.out.print("dTime: " + delta + "ns ");

    // then verify the queue
    if (queue.isEmpty()) {
      System.out.println("[PASSED] Queue is empty after simultaneous add-remove");
      final Integer[] elements = removedElements.toArray(new Integer[removedElements.size()]);
      Arrays.sort(elements, (lhs, rhs) -> lhs - rhs);
      for (int i = 0; i < elements.length; ++i) {
        if (i != elements[i]) {
          throw new AssertionError("Element " + i + " doesn't match: " + elements[i]);
        }
      }
    } else {
      System.out.println("[FAILED] Queue is not empty, queueSize=" + queue.size());
    }
  }

  private void addElementsToQueueAndVerify() {
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
    final Integer[] elements = queue.toArray(new Integer[queue.size()]);
    if (elements.length == numThreads) {
      System.out.println("[PASSED] Queue contains the same amount of elements that have been passed");
      Arrays.sort(elements, (lhs, rhs) -> lhs - rhs);
      for (int i = 0; i < elements.length; ++i) {
        if (i != elements[i]) {
          throw new AssertionError("Element " + i + " doesn't match: " + elements[i]);
        }
      }
    } else {
      System.out.println("[FAILED] Queue contains different amount of elements that have been passed, actual=" +
          elements.length + ", expected=" + numThreads);
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
