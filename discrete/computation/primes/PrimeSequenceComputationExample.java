import java.util.ArrayList;
import java.util.List;

/**
 * Prime computation using my own, probably reinvented, memory unfriendly variation of Erathosphen sieve.
 * <pre>
 * First 100 primes are:
 *  2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71 73 79 83 89 97 101 103 107 109 113 127 131 137
 *  139 149 151 157 163 167 173 179 181 191 193 197 199 211 223 227 229 233 239 241 251 257 263 269 271 277
 *  281 283 293 307 311 313 317 331 337 347 349 353 359 367 373 379 383 389 397 401 409 419 421 431 433 439
 *  443 449 457 461 463 467 479 487 491 499 503 509 521 523 541
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class PrimeSequenceComputationExample {

  public static void main(String[] args) {
    demo(100);
    demo(1000);
  }

  public static void demo(int limit) {
    System.out.println("First " + limit + " primes are:");
    final Sieve sieve = new Sieve(limit);
    int len = 0;
    while (sieve.residues.size() < limit) {
      final long nextPrime = sieve.findNext();
      final String str = " " + nextPrime;
      System.out.print(str);
      len += str.length();
      if (len > 100) {
        System.out.println();
        len = 0;
      }
    }
    System.out.println();
  }

  private static final class Sieve {
    private final List<PrimeResidue> residues;

    public Sieve(int primeCountEstimation) {
      this.residues = new ArrayList<>(primeCountEstimation);
    }

    public long findNext() {
      for (;;) {
        boolean zeroMet = false;
        //noinspection ForLoopReplaceableByForEach
        for (int i = 0; i < residues.size(); ++i) {
          final PrimeResidue primeResidue = residues.get(i);
          ++primeResidue.residue;
          if (primeResidue.residue == primeResidue.prime) {
            primeResidue.residue = 0;
            zeroMet = true;
          }
        }

        if (!zeroMet) {
          final long result;
          if (!residues.isEmpty()) {
            final PrimeResidue last = residues.get(residues.size() - 1);
            // Should always work according to Bertrand–Chebyshev theorem
            result = last.prime + last.residue;
          } else {
            result = 2;
          }
          residues.add(new PrimeResidue(result));
          return result;
        }
      }
    }
  }

  private static final class PrimeResidue {
    private final long prime;
    private long residue = 0;

    public PrimeResidue(long prime) {
      this.prime = prime;
    }
  }
}
