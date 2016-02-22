/**
 * Sample run:
 * <pre>
 * Neg2 representation of 0 is 0
 * Neg2 representation of 1 is 1
 * Neg2 representation of 2 is 110
 * Neg2 representation of 3 is 111
 * Neg2 representation of 4 is 100
 * Neg2 representation of 5 is 101
 * Neg2 representation of 6 is 11010
 * Neg2 representation of 7 is 11011
 * Neg2 representation of 8 is 11000
 * Neg2 representation of 16 is 10000
 * Neg2 representation of -1 is 11
 * Neg2 representation of -2 is 10
 * Neg2 representation of -3 is 1101
 * Neg2 representation of -4 is 1100
 * Neg2 representation of -5 is 1111
 * Neg2 representation of -6 is 1110
 * Neg2 representation of -7 is 1001
 * Neg2 representation of -8 is 1000
 * Neg2 representation of -12 is 110100
 * </pre>
 * @author Alexander Shabanov
 */
public final class Neg2RepresentationExample {

  public static void main(String[] args) {
    demo(0);
    demo(1);
    demo(2);
    demo(3);
    demo(4);
    demo(5);
    demo(6);
    demo(7);
    demo(8);
    demo(16);
    demo(-1);
    demo(-2);
    demo(-3);
    demo(-4);
    demo(-5);
    demo(-6);
    demo(-7);
    demo(-8);
    demo(-12);
  }

  public static void demo(int num) {
    System.out.println("Neg2 representation of " + num + " is " + getNeg2Representation(num));
  }

  public static String getNeg2Representation(int num) {
    if (num == 0) {
      return "0";
    }

    int sgn = -1;
    final StringBuilder sb = new StringBuilder();
    while (num != 0) {
      if ((num & 1) != 0) {
        num = num + sgn;
        sb.append('1');
      } else {
        sb.append('0');
      }
      num = num / 2;
      sgn = -sgn;
    }

    sb.reverse();
    return sb.toString();
  }
}
