import util.LockFreeQueueVerifier;

import java.util.AbstractQueue;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Illustration of lock-free queue based on circular, fixed-size buffer.
 */
public final class FixedSizeLockFreeQueueExample {

  public static void main(String[] args) {
    final Queue<Integer> q = new FixedSizeLockFreeQueue<>(2000);
    new LockFreeQueueVerifier(1000, q).start();
    printStats(q);
    new LockFreeQueueVerifier(1000, q).start();
    printStats(q);
  }

  //
  // Private
  //

  private static void printStats(Queue<?> queue) {
    if (queue instanceof FixedSizeLockFreeQueue) {
      final FixedSizeLockFreeQueue<?> q = (FixedSizeLockFreeQueue) queue;
      System.out.println("[STATS] Acquiring Attempts=" + q.getModAcquiringAttempts());
    }
  }

  /**
   * Lock-free implementation of queue based on circular, fixed-size buffer.
   *
   * @param <E> Queue element type
   */
  private static final class FixedSizeLockFreeQueue<E> extends AbstractQueue<E> {
    private final Object[] buffer;
    private volatile int head = 0;
    private volatile int tail = 0;

    private final AtomicInteger mods = new AtomicInteger(0);
    private final AtomicInteger modGuard = new AtomicInteger(0);

    private final AtomicLong modAcquiringAttempts = new AtomicLong(0); // statistics

    public FixedSizeLockFreeQueue(int maxSize) {
      this.buffer = new Object[maxSize];
    }

    public long getModAcquiringAttempts() {
      return modAcquiringAttempts.get();
    }

    @SuppressWarnings("NullableProblems")
    @Override
    public Iterator<E> iterator() {
      int h = head;
      final int t = tail;
      final int size = h > t ? t + buffer.length - h : t - h;
      final Iterator<?> result;
      if (size == 0) {
        result = Collections.emptyIterator();
      } else {
        final List<Object> l = new ArrayList<>(size);
        while (h != t) {
          l.add(buffer[h]);
          h = (h + 1) % buffer.length;
        }

        //noinspection unchecked
        result = l.iterator();
      }

      //noinspection unchecked
      return (Iterator<E>) result;
    }

    @Override
    public int size() {
      final int h = head;
      final int t = tail;
      return h > t ? t + buffer.length - h : t - h;
    }

    @Override
    public boolean offer(E e) {
      // Lock start
      final int mod = mods.incrementAndGet();
      long attempts = 0;
      while (!modGuard.compareAndSet(0, mod)) {
        ++attempts;
      }

      final boolean succeeded;
      final int t = tail;
      final int newTail = (t + 1) % buffer.length;
      if (head == newTail) {
        succeeded = false;
      } else {
        buffer[t] = e;
        succeeded = true;
        tail = newTail;
      }

      // Lock end
      modGuard.set(0);

      modAcquiringAttempts.addAndGet(attempts); // statistics

      return succeeded;
    }

    @Override
    public E poll() {
      // Lock start
      final int mod = mods.incrementAndGet();
      long attempts = 0;
      while (!modGuard.compareAndSet(0, mod)) {
        ++attempts;
      }

      int h = head;
      int t = tail;

      final Object result;
      if (h == t) {
        result = null;
      } else {
        result = buffer[h];
        head = (h + 1) % buffer.length;
      }

      // Lock end
      modGuard.set(0);

      modAcquiringAttempts.addAndGet(attempts); // statistics

      //noinspection unchecked
      return result == null ? null : (E) result;
    }

    @Override
    public E peek() {
      // Lock start
      final int mod = mods.incrementAndGet();
      long attempts = 0;
      while (!modGuard.compareAndSet(0, mod)) {
        ++attempts;
      }

      int h = head;
      int t = tail;

      final Object result;
      if (h == t) {
        result = null;
      } else {
        result = buffer[h];
      }

      // Lock end
      modGuard.set(0);

      modAcquiringAttempts.addAndGet(attempts); // statistics

      //noinspection unchecked
      return result == null ? null : (E) result;
    }
  }
}
