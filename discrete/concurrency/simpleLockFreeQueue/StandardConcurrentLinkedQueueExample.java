import util.LockFreeQueueVerifier;

import java.util.concurrent.ConcurrentLinkedQueue;

/**
 * @author Alexander Shabanov
 */
public final class StandardConcurrentLinkedQueueExample {
  public static void main(String[] args) {
    final LockFreeQueueVerifier verifier = new LockFreeQueueVerifier(1000, new ConcurrentLinkedQueue<>());
    verifier.start();
  }
}
