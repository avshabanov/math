package problems.leet100.nthMagicalNumber;

import java.math.BigInteger;

/**
 * 878. Nth Magical Number
 * https://leetcode.com/problems/nth-magical-number/
 * <p>A positive integer is magical if it is divisible by either A or B.
 * Return the N-th magical number.  Since the answer may be very large, return it modulo 10^9 + 7.
 *
 * Example 1:
 * Input: N = 1, A = 2, B = 3
 * Output: 2
 *
 * Example 2:
 * Input: N = 4, A = 2, B = 3
 * Output: 6
 *
 * Example 3:
 * Input: N = 5, A = 2, B = 4
 * Output: 10
 *
 * Example 4:
 * Input: N = 3, A = 6, B = 4
 * Output: 8
 *
 * Note:
 * 1 <= N <= 10^9
 * 2 <= A <= 40000
 * 2 <= B <= 40000
 * </p>
 */
public class NthMagicalNumberSolution {

  public static void main(String[] args) {
    demo(1000000000, 40000, 40000);

    demo(859, 759, 30);
    demo(10, 10, 8);
    demo(3, 8, 3);
    demo(10, 9, 4);

    demo(1, 2, 3);
    demo(4, 2, 3);
    demo(5, 2, 4);

    demo(3, 6, 4);

  }

  private static void demo(int n, int a, int b) {
    final int magicalNumber = bruteForceNthMagicalNumber(n, a, b);
    final int magicalNumber2 = nthMagicalNumber(n, a, b);
    System.out.printf(
        "Input: N = %d, A = %d, B = %d\nOutput: %d, Output2: %d\n---\n",
        n, a, b,
        magicalNumber,
        magicalNumber2);
  }

  private static int bruteForceNthMagicalNumber(int n, int a, int b) {
    if (a == b) {
      // shortcut for the same a
      return nthMagicalNumber(n, a);
    }

    // complex scenario: a != b
    // normalize, so a is the smallest and b is the greatest
    if (a > b) {
      int tmp = a;
      a = b;
      b = tmp;
    }

    if (b % a == 0) {
      return nthMagicalNumber(n, a);
    }

    int aCandidate = a;
    int bCandidate = b;

    int current = 0;
    for (int i = 0; i < n; ++i) {
      if (aCandidate < bCandidate) {
        current = aCandidate;
        aCandidate += a;
      } else if (aCandidate > bCandidate) {
        current = bCandidate;
        bCandidate += b;
      } else {
        current = aCandidate;
        aCandidate += a;
        bCandidate += b;
      }
    }

    return current;
  }

  //
  // Optimized version of find-nth-magical-number:
  //

  private static int nthMagicalNumber(int n, int a, int b) {
    if (a == b) {
      // shortcut for the same a
      return nthMagicalNumber(n, a);
    }

    // complex scenario: a != b
    // normalize, so a is the smallest and b is the greatest
    if (a > b) {
      int tmp = a;
      a = b;
      b = tmp;
    }

    if (b % a == 0) {
      return nthMagicalNumber(n, a);
    }

    final int gcd = BigInteger.valueOf(a).gcd(BigInteger.valueOf(b)).intValueExact();
    final long kPrime = (((long) n) * a * b) / (a + b - gcd);
    final long nPrime = kPrime / a + kPrime / b - (kPrime * gcd) / (a * b);
    final long result = findK(nPrime, kPrime, gcd, n, a, b);
    return (int) (result % MODULO);
  }

  private static long findK(long nPrime, long kPrime, long gcd, int n, int a, int b) {
    long amod = kPrime % a;
    long bmod = kPrime % b;

    System.out.printf("\t[DBG] k1 = %d (n1' = %d; amod=%d, bmod=%d)\n", kPrime, nPrime, amod, bmod);

    if (nPrime < n) {
      amod = kPrime - amod + a;
      bmod = kPrime - bmod + b;
      for (long k;;) {
        if (amod < bmod) {
          k = amod;
          amod += a;
        } else if (amod > bmod) {
          k = bmod;
          bmod += b;
        } else {
          k = amod;
          amod += a;
          bmod += b;
        }

        nPrime = k / a + k / b - (k * gcd) / (a * b);
        if (nPrime == n) {
          return k;
        }

        if (nPrime > n) {
          throw new IllegalStateException("nPrime > n");
        }
      }
    }

    if (nPrime == n && ((amod == 0 || bmod == 0))) {
      // exact match found
      return kPrime;
    }

    // direction: down
    amod = kPrime - amod;
    bmod = kPrime - bmod;
    for (long k;;) {
      if (amod > bmod) {
        k = amod;
        amod -= a;
      } else if (amod < bmod) {
        k = bmod;
        bmod -= b;
      } else {
        k = amod;
        amod -= a;
        bmod -= b;
      }

      nPrime = k / a + k / b - (k * gcd) / (a * b);
      if (nPrime == n) {
        return k;
      }

      if (nPrime < n) {
        throw new IllegalStateException("nPrime < n");
      }
    }
  }

  private static int nthMagicalNumber(int n, int a) {
    // shortcut for simple scenario when a equals to b
    long result = 0;
    long pow = 1;
    for (; n > 0; n = n >> 1) {
      if ((n & 1) != 0) {
        result = (result + a * pow) % MODULO;
      }
      pow *= 2;
    }

    return (int) result;
  }

  private static final int MODULO = 1_000_000_007;
}
