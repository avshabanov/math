/**
 * @author Alexander Shabanov
 */
public final class ReversalInductionTowerOfHanoiExample {

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
    p.move(Rod.R1, Rod.R2, Rod.R3, depth);
  }

  private enum Rod {
    R1,
    R2,
    R3
  }

  private static abstract class SolutionFinder {
    public final void move(Rod source, Rod medium, Rod target, int depth) {
      if (depth < 0) {
        throw new IllegalArgumentException("Negative depth");
      } else if (depth == 0) {
        return; // nothing to move
      }

      // NOTE: use the fact that N solution is could be a combination of:
      //  (N-1) solution applied to source rod as source, medium rod as target, and target rod as medium,
      //  plus moving rod from source to target
      //  plus (N-1) solution applied to source rod as medium, medium rod as source and target rod as target
      move(source, target, medium, depth - 1);
      recordMove(source, target, depth);
      move(medium, source, target, depth - 1);
    }

    protected abstract void recordMove(Rod from, Rod to, int disk);
  }

  private static final class OnScreenSolutionPrinter extends SolutionFinder {

    @Override
    protected void recordMove(Rod from, Rod to, int disk) {
      System.out.printf("\tMove disk %d from %s to %s\n", disk, from, to);
    }
  }
}
