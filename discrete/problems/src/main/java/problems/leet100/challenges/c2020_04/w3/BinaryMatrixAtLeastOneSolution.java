package problems.leet100.challenges.c2020_04.w3;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;

/**
 * https://leetcode.com/explore/challenge/card/30-day-leetcoding-challenge/530/week-3/3306/
 * <p>Given a row-sorted binary matrix binaryMatrix, return leftmost column index(0-indexed) with at least a 1 in it.
 * If such index doesn't exist, return -1.</p>
 *
 * NB: this solution is adapted to a custom bitset matrix type that differs from the one declared in the interactive
 * session.
 */
public class BinaryMatrixAtLeastOneSolution {

  public static final class Demo1 {

    public static void main(String[] args) {
      final BitSetDenseMatrix bsdMatrix = new BitSetDenseMatrix(3, 2);
      bsdMatrix.set("" +
          "000" +
          "011"
      );
      System.out.printf("Matrix %s:\n", bsdMatrix.dimensions());
      bsdMatrix.printMatrix(System.out);

      System.out.printf("Min column: %d\n", leftMostColumnWithOne(bsdMatrix));
    }
  }

  public static final class Demo2 {

    public static void main(String[] args) {
      final BitSetDenseMatrix bsdMatrix = new BitSetDenseMatrix(2, 2);
      bsdMatrix.set("" +
          "00" +
          "11"
      );
      System.out.printf("Matrix %s:\n", bsdMatrix.dimensions());
      bsdMatrix.printMatrix(System.out);

      System.out.printf("Min column: %d\n", leftMostColumnWithOne(bsdMatrix));
    }
  }

  private interface BinaryMatrix {
    int get(int x, int y);
    List<Integer> dimensions();
  }

  private static final class BitSetDenseMatrix implements BinaryMatrix {
    private final int width;
    private final int height;
    private final BitSet bitSet;

    public BitSetDenseMatrix(int width, int height) {
      this.width = width;
      this.height = height;
      this.bitSet = new BitSet(width * height);
    }

    public void set(int x, int y, int element) {
      bitSet.set(computeIndex(x, y), element > 0);
    }

    public void set(String s) {
      if (s.length() != width * height) {
        throw new IllegalArgumentException("wrong dimensions");
      }
      for (int i = 0; i < width * height; ++i) {
        set(i % width, i / width, s.charAt(i) == '1' ? 1 : 0);
      }
    }

    @Override public int get(int x, int y) {
      return bitSet.get(computeIndex(x, y)) ? 1 : 0;
    }

    @Override public List<Integer> dimensions() {
      return Arrays.asList(width, height);
    }

    public void printMatrix(PrintStream ps) {
      for (int h = 0; h < height; ++h) {
        for (int w = 0; w < width; ++w) {
          ps.print(get(w, h));
        }
        ps.print("\n");
      }
    }

    private int computeIndex(int x, int y) {
      if (x < 0 || x >= width) {
        throw new IllegalArgumentException("x");
      }
      if (y < 0 || y >= height) {
        throw new IllegalArgumentException("y");
      }
      return y * width + x;
    }
  }

  private static int leftMostColumnWithOne(BinaryMatrix binaryMatrix) {
    final List<Integer> dims = binaryMatrix.dimensions();
    if (dims.size() != 2 || dims.get(0) < 1 || dims.get(1) < 1) {
      return -1;
    }

    final int width = dims.get(0);
    final int height = dims.get(1);

    int px = width - 1;
    int py = 0;

    int column = width;

    while (px >= 0 && py < height) {
      if (binaryMatrix.get(px, py) == 0) {
        if (py < (height - 1)) {
          ++py; // move to the row beneath this column
          continue;
        }
      } else {
        // found min column
        column = px;
      }

      --px;
    }

    return column < width ? column : -1;
  }
}
