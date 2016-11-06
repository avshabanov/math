import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * PROBLEM:
 * <pre>
 * Given a rectangular board where every cell has assigned positive integer score and a chip in bottom left
 * corner move that chip on this board to the top right corner. Chip is allowed to move by one cell in either top
 * or right direction. Find a path that yields biggest score.
 * </pre>
 * <p>
 * Sample output:
 * </p>
 * <pre>
 * Optimal path=[(0, 2), (1, 2), (1, 1), (1, 0)] with score=910 for board:
 *   100    0
 *    30   10
 *     0  900
 * ---
 *
 * Optimal path=[(0, 3), (1, 3), (2, 3), (2, 2), (2, 1), (2, 0), (3, 0)] with score=700 for board:
 *   100  100  200    0
 *   100  100  100  100
 *   100  100  100  100
 *     0  100  200  100
 * ---
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class TreasureTroveExample {

  public static void main(String[] args) {
    demo1();
    demo2();
  }

  public static void demo1() {
    final Board b = new BoardImpl(2, 3);
    b.set(0, 0, 100).set(1, 0, 0);
    b.set(0, 1, 30).set(1, 1, 10);
    b.set(0, 2, 0).set(1, 2, 900);

    findOptimalPath(b);
  }

  public static void demo2() {
    final Board b = new BoardImpl(4, 4);
    b.set(0, 0, 100).set(1, 0, 100).set(2, 0, 200).set(3, 0,   0);
    b.set(0, 1, 100).set(1, 1, 100).set(2, 1, 100).set(3, 1, 100);
    b.set(0, 2, 100).set(1, 2, 100).set(2, 2, 100).set(3, 2, 100);
    b.set(0, 3,   0).set(1, 3, 100).set(2, 3, 200).set(3, 3, 100);

    findOptimalPath(b);
  }

  public static void findOptimalPath(Board b) {
    final Finder finder = new Finder(b);
    finder.find(new Cell(0, b.getHeight() - 1));
    System.out.println("Optimal path=" + finder.candidatePath + " with score=" + finder.candidateWeigth +
        " for board:\n" + b.toString() + "---\n");
  }

  public static final class Finder {
    final Board board;

    final List<Cell> path = new ArrayList<>();
    int weight = 0;

    List<Cell> candidatePath = null;
    int candidateWeigth = 0;

    public Finder(Board board) {
      this.board = board;
    }

    public void find(Cell c) {
      final int cellWeight = board.get(c.w, c.h);
      final int cellIndex = path.size();
      weight += cellWeight;
      path.add(c);

      // try right
      if (c.w < board.getRightBound()) {
        find(new Cell(c.w + 1, c.h));
      }

      // try left
      if (c.h > 0) {
        find(new Cell(c.w, c.h - 1));
      }

      // destination check
      if ((c.w == board.getRightBound()) && (c.h == 0) && (weight > candidateWeigth)) {
        candidatePath = Collections.unmodifiableList(Arrays.asList(path.toArray(new Cell[path.size()])));
        candidateWeigth = weight;
      }

      // rollback
      weight -= cellWeight;
      path.remove(cellIndex);
    }
  }

  public static final class Cell {
    final int w;
    final int h;

    Cell(int w, int h) {
      this.w = w;
      this.h = h;
    }

    @Override
    public String toString() {
      return "(" + w + ", " + h + ")";
    }
  }

  private interface Board {
    default int getRightBound() {
      return getWidth() - 1;
    }

    int getWidth();
    int getHeight();

    int get(int w, int h);
    Board set(int w, int h, int value);
  }

  private static final class BoardImpl implements Board {
    final int[] arr;
    final int width;
    final int height;

    BoardImpl(int width, int height) {
      if (width <= 0 || height <= 0) {
        throw new IllegalArgumentException();
      }
      this.arr = new int[width * height];
      this.width = width;
      this.height = height;
    }

    @Override
    public int getWidth() {
      return width;
    }

    @Override
    public int getHeight() {
      return height;
    }

    @Override
    public int get(int w, int h) {
      return arr[getIndex(w, h)];
    }

    @Override
    public Board set(int w, int h, int value) {
      arr[getIndex(w, h)] = value;
      return this;
    }

    int getIndex(int w, int h) {
      if (w < 0 || w >= width || h < 0 || h >= height) {
        throw new IllegalArgumentException();
      }
      return h * width + w;
    }

    @Override
    public String toString() {
      final StringBuilder sb = new StringBuilder();
      for (int h = 0; h < getHeight(); ++h) {
        for (int w = 0; w < getWidth(); ++w) {
          sb.append(' ').append(String.format("%4s", get(w, h)));
        }
        sb.append('\n');
      }
      return sb.toString();
    }
  }
}
