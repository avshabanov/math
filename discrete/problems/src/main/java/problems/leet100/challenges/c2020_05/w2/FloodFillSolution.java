package problems.leet100.challenges.c2020_05.w2;

import java.util.Arrays;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/535/week-2-may-8th-may-14th/3326/
 * <p>An image is represented by a 2-D array of integers, each integer representing the pixel value of
 * the image (from 0 to 65535).
 * Given a coordinate (sr, sc) representing the starting pixel (row and column) of the flood fill, and a
 * pixel value newColor, "flood fill" the image.
 *
 * To perform a "flood fill", consider the starting pixel, plus any pixels connected 4-directionally to the
 * starting pixel of the same color as the starting pixel, plus any pixels connected 4-directionally to those
 * pixels (also with the same color as the starting pixel), and so on.
 * Replace the color of all of the aforementioned pixels with the newColor.
 *
 * At the end, return the modified image.</p>
 * <p>Note:
 *
 * The length of image and image[0] will be in the range [1, 50].
 * The given starting pixel will satisfy 0 <= sr < image.length and 0 <= sc < image[0].length.
 * The value of each color in image[i][j] and newColor will be an integer in [0, 65535].</p>
 */
public class FloodFillSolution {

  public static final class Demo0 {
    public static void main(String[] args) {
      final int[][] input = {{0}};
      final int[][] result = floodFill(input, 0, 0, 1);

      System.out.println("Input:");
      print2D(input);

      System.out.println("Output:");
      print2D(result);
    }
  }

  public static final class Demo1 {
    public static void main(String[] args) {
      final int[][] input = {{1,1,1},{1,1,0},{1,0,1}};
      final int[][] result = floodFill(input, 1, 1, 2);

      System.out.println("Input:");
      print2D(input);

      System.out.println("Output:");
      print2D(result);
    }
  }

  public static final class Demo3 {
    public static void main(String[] args) {
      final int[][] input = {{0,0,0},{0,1,1}};
      final int[][] result = floodFill(input, 1, 1, 1);

      System.out.println("Input:");
      print2D(input);

      System.out.println("Output:");
      print2D(result);
    }
  }

  private static void print2D(int[][] input) {
    for (int[] ints : input) {
      for (int anInt : ints) {
        System.out.printf("%d", anInt);
      }
      System.out.println();
    }
  }

  private static int[][] floodFill(int[][] image, int sr, int sc, int newColor) {
    final Filler filler = new Filler(image, sr, sc, newColor);
    filler.fill(sc, sr);

    // finally invert negatives
    for (int[] slice : filler.target) {
      for (int i = 0; i < slice.length; ++i) {
        if (slice[i] < 0) {
          slice[i] = -slice[i];
        }
      }
    }

    return filler.target;
  }

  private static final class Filler {
    final int width;
    final int height;
    final int[][] target;
    final int startColor;
    final int newColor;

    public Filler(int[][] image, int sr, int sc, int newColor) {
      this.width = image[0].length;
      this.height = image.length;
      this.target = new int[height][];
      for (int h = 0; h < height; ++h) {
        this.target[h] = Arrays.copyOf(image[h], width);
      }
      this.startColor = image[sr][sc];
      this.newColor = newColor;
    }

    void fill(int x, int y) {
      if (target[y][x] != startColor) {
        return;
      }
      target[y][x] = -newColor;
      if (x > 0) {
        fill(x - 1, y);
      }
      if (x < (width - 1)) {
        fill(x + 1, y);
      }
      if (y > 0) {
        fill(x, y - 1);
      }
      if (y < (height - 1)) {
        fill(x, y + 1);
      }
    }
  }
}
