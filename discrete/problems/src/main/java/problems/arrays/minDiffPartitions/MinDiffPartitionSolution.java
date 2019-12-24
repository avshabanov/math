package problems.arrays.minDiffPartitions;

import java.util.Arrays;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public final class MinDiffPartitionSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      demo(new int[]{1,2,3,4});
      demo(new int[]{1,2,3,4,5});
      demo(new int[]{1,2,3,4,100});
    }
  }

  private static void demo(int[] source) {
    final Result r = new MinDiffPartitionSolution(source).find();
    final int leftSum = Arrays.stream(r.left).sum();
    final int rightSum = Arrays.stream(r.right).sum();
    System.out.printf(
        "Source array %s can be partitioned into %s (sum=%d) and %s (sum=%d); sum diff=%d\n",
        Arrays.toString(source),
        Arrays.toString(r.left),
        leftSum,
        Arrays.toString(r.right),
        rightSum,
        Math.abs(rightSum - leftSum)
    );
  }

  private final int[] source;
  private final int[] leftIndices;
  private int leftSum;

  private int[] minLeftIndices;
  private int minLeftSum = Integer.MAX_VALUE;
  private int minRightSum = 0;

  private int sum;

  private MinDiffPartitionSolution(int[] source) {
    this.source = source;
    final int leftSize = source.length / 2;
    this.leftIndices = new int[leftSize];
    this.sum = Arrays.stream(source).sum();
  }


  private void findSum(int sourcePos, int leftPos) {
    boolean canFitLeft = true;
    for (int i = sourcePos; i < source.length && canFitLeft; ++i) {
      final int num = source[i];
      sum -= num;
      leftSum += num;
      leftIndices[leftPos] = i;
      final int nextLeftPos = leftPos + 1;
      if (nextLeftPos == this.leftIndices.length) {
        final int currentDiff = Math.abs(sum - leftSum);
        // copy current solution
        if (currentDiff < Math.abs(minLeftSum - minRightSum)) {
          minLeftIndices = Arrays.copyOf(leftIndices, leftIndices.length);
          minLeftSum = leftSum;
          minRightSum = sum;
        }
      } else {
        if ((leftIndices.length - nextLeftPos) > (source.length - i)) {
          canFitLeft = false;
        } else {
          findSum(i + 1, leftPos + 1);
        }
      }

      // recover sum
      sum += num;
      leftSum -= num;
    }
  }

  static final class Result {
    final int[] left;
    final int[] right;

    Result(int[] left, int[] right) {
      this.left = left;
      this.right = right;
    }
  }

  Result find() {
    findSum(0, 0);

    final Set<Integer> rightIndices = IntStream.range(0, source.length).boxed().collect(Collectors.toSet());
    rightIndices.removeAll(Arrays.stream(minLeftIndices).boxed().collect(Collectors.toList()));

    return new Result(
        Arrays.stream(minLeftIndices).map(i -> source[i]).toArray(),
        rightIndices.stream().mapToInt(i -> source[i]).toArray()
    );
  }
}
