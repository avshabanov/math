package problems.computations;

/**
 * Each triangle's vertex is connected to some point inside the triangle, so it breaks triangle's angles in 6 parts.
 * Starting with some angle and going clockwise it yields the following angles, so that each angle is a natural number
 * expressed in degrees: m, 8, n, 41, k, 33.
 *
 * Find m, n and k, assuming that these are natural numbers (when expressed in degrees) and m < n < k.
 */
class TriangleHalfAngles {

  private static final int HALF_REV_DEGREES = 180;
  private static final double DEGREE_TO_RADIAN = Math.PI / HALF_REV_DEGREES;
  private static final double EPSILON = 0.0000001;

  private static boolean eq(double lhs, double rhs) {
    return Math.abs(lhs - rhs) < EPSILON;
  }

  private static double sin(int d) {
    return Math.sin(d * DEGREE_TO_RADIAN);
  }

  public static void main(String[] args) {
    final int mPrime = 8, nPrime = 41, kPrime = 33;
    final int mnkDegreesSum = HALF_REV_DEGREES - (mPrime + nPrime + kPrime);

    final double target = sin(mPrime) * sin(nPrime) * sin(kPrime);
    for (int m = 1; m < mnkDegreesSum / 3; ++m) {
      final int nMax = (mnkDegreesSum - m) / 2;
      for (int n = m + 1; n < nMax; n++) {
        final int k = mnkDegreesSum - m - n;
        if (eq(target, sin(m) * sin(n) * sin(k))) {
          System.out.printf("Found solution: m=%d, n=%d, k=%d\n", m, n, k); // Solution: m=11, n=16, k=71
        }
      }
    }
  }
}
