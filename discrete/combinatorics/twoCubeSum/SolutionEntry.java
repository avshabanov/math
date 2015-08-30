
public class SolutionEntry {
  final long a, b, c, d;

  public SolutionEntry(long a, long b, long c, long d) {
    this.a = a;
    this.b = b;
    this.c = c;
    this.d = d;
  }

  @Override
  public String toString() {
    return "{ " + a + "^3 + " + b + "^3 = " + c + "^3 + " + d + "^3 }";
  }
}
