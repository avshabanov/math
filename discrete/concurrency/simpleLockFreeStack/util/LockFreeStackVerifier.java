package util;

import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * Verification code for lock free stack examples.
 */
public final class LockFreeStackVerifier {
  private final int numThreads;
  private final LockFreeStack<Integer> stack;

  public LockFreeStackVerifier(int numThreads, LockFreeStack<Integer> stack) {
    this.numThreads = numThreads;
    this.stack = stack;
  }

  public void start() {
    addElementsToStackAndVerify();
    removeElementsFromStackAndVerify();
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
          stack.push(num);
          stopGate.countDown(); // signal that operation has been completed
        } catch (InterruptedException e) {
          System.err.println("Unexpected interruption of push thread #" + num);
          Thread.currentThread().interrupt();
        }
      });

      thread.start();
    }

    // signal that all threads can start modifying stack simultaneously
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

    // then verify the stack
    final List<Integer> elements = stack.toList();
    if (elements.size() == numThreads) {
      System.out.println("[PASSED] Stack contains the same amount of elements that have been passed");
    } else {
      System.out.println("[FAILED] Stack contains different amount of elements that have been passed, actual=" +
          elements.size() + ", expected=" + numThreads);
    }
  }



  private void removeElementsFromStackAndVerify() {
    final int numElements = stack.size();
    final CountDownLatch startGate = new CountDownLatch(1);
    final CountDownLatch stopGate = new CountDownLatch(numElements);
    final AtomicInteger popFailures = new AtomicInteger(0);

    for (int i = 0; i < numElements; ++i) {
      final int threadIndex = i;
      final Thread thread = new Thread(() -> {
        try {
          startGate.await();
          final Integer result = stack.pop(null);
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

    // signal that all threads can start modifying stack simultaneously
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

    // then verify the stack
    final List<Integer> elements = stack.toList();
    if (elements.size() == 0) {
      System.out.println("[PASSED] Stack is now empty");
    } else {
      System.out.println("[FAILED] Stack is not empty, size=" + elements.size() +
          ", countOfPopFailures=" + popFailures.get());
    }
  }
}
