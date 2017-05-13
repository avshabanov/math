import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Objects;

/**
 * Stack-based solver for tower-of-hanoi problem
 */
public final class StackBasedTowerOfHanoiExample {
  public static void main(String[] args) {
    demo(1);
    demo(2);
    demo(3);
    demo(4);
    demo(5);
  }

  private static void demo(int depth) {
    System.out.printf("Solution for depth=%d:\n", depth);
    final OnScreenSolutionPrinter p = new OnScreenSolutionPrinter();
    p.solve(Rod.S, Rod.M, Rod.T, depth);
  }

  private enum Rod {
    S,
    M,
    T
  }

  private interface Move {
  }

  private static final class CompleteMove implements Move {
    final Rod from;
    final Rod to;
    final int disk;

    CompleteMove(Rod from, Rod to, int disk) {
      if (disk <= 0) {
        throw new IllegalArgumentException("disk");
      }

      this.from = Objects.requireNonNull(from);
      this.to = Objects.requireNonNull(to);
      this.disk = disk;
    }
  }

  private static final class IncompleteMove implements Move {
    final Rod source;
    final Rod medium;
    final Rod target;
    final int largestDisk;

    IncompleteMove(Rod source, Rod medium, Rod target, int largestDisk) {
      if (largestDisk <= 0) {
        throw new IllegalArgumentException("largestDisk");
      }

      this.source = Objects.requireNonNull(source);
      this.medium = Objects.requireNonNull(medium);
      this.target = Objects.requireNonNull(target);
      this.largestDisk = largestDisk;
    }
  }

  private static abstract class SolutionFinder {

    final void solve(Rod source, Rod medium, Rod target, int largestDisk) {
      if (largestDisk <= 0) {
        return;
      }

      final Deque<Move> moves = new ArrayDeque<>(2 * ceilLog2(largestDisk) /* upper bound for estimated */);
      moves.push(new IncompleteMove(source, medium, target, largestDisk));

      while (!moves.isEmpty()) {
        final Move move = moves.pop();
        if (move instanceof CompleteMove) {
          final CompleteMove m = (CompleteMove) move;
          this.registerMove(m.from, m.to, m.disk);
        } else {
          final IncompleteMove m = (IncompleteMove) move;
          if (m.largestDisk > 1) {
            final int nextLargestDisk = m.largestDisk - 1;
            moves.push(new IncompleteMove(m.medium, m.source, m.target, nextLargestDisk));
            moves.push(new CompleteMove(m.source, m.target, m.largestDisk));
            moves.push(new IncompleteMove(m.source, m.target, m.medium, nextLargestDisk));
          } else {
            this.registerMove(m.source, m.target, m.largestDisk);
          }
        }
      }
    }

    abstract void registerMove(Rod from, Rod to, int disk);
  }

  private static final class OnScreenSolutionPrinter extends SolutionFinder {

    @Override
    void registerMove(Rod from, Rod to, int disk) {
      System.out.printf("\tMove disk %d from %s to %s\n", disk, from, to);
    }
  }

  private static int ceilLog2(int value) {
    if (value <= 0) {
      throw new IllegalArgumentException("value should be positive");
    }
    return Integer.SIZE - Integer.numberOfLeadingZeros(value);
  }
}
