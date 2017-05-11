/**
 * Demonstrates how to swap two numbers without need for additional variables.
 */
public final class InplaceSwapDemo {

  public static void main(String[] args) {
    inplaceSwap(1, 2);
    inplaceSwap(-2, -1);
  }

  private static void inplaceSwap(int a, int b) {
    System.out.printf("source: a=%d b=%d", a, b);

    b += a; // b2 = a + b
    a -= b; // a2 = -b
    b += a; // b3 = a
    a = -a; // a3 = b

    System.out.printf(", target: a=%d b=%d\n", a, b);
  }
}
