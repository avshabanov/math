package approx.basel

import java.util.ArrayList
import java.math.BigDecimal
import java.math.BigInteger
import java.util.HashSet

data class Ratio private (val numerator : Int, val denominator : Int) {
  class object {
    fun invoke(numerator : Int, denominator : Int) : Ratio {
      val gcd = BigInteger.valueOf(numerator.toLong()).gcd(BigInteger.valueOf(denominator.toLong())).intValue();
      return Ratio(numerator / gcd, denominator / gcd)
    }
  }

  // this enables clients to write `a * b` for two ratios
  fun times(other: Ratio) = invoke(this.numerator * other.numerator, this.denominator * other.denominator)

  // custom toString(), the automatically generated one would be giving "Ratio(numerator=2, denominator=3)"
  override fun toString() = "$numerator/$denominator"
}

fun approx(value : Double, base : Double, epsilon : Double = 0.000001, ratioLim : Int = 10000) : Collection<Ratio> {
  val result = HashSet<Ratio>()
  for (denom in 1..ratioLim) {
    for (num in 1..ratioLim) {
      val x = base * num / denom
      if (x > value) {
        break
      } else if (Math.abs(value - x) < epsilon) {
        result.add(Ratio(numerator = num, denominator = denom))
      }
    }
  }
  return result
}

fun ratioTest() {
  val r = Ratio(2, 3)
  val r2 = r.copy(numerator = 5)
  val r3 = r * r2

  println("r = ${r}, r2 = ${r2}, r3 = ${r3}")
}

fun main(args: Array<String>) {
  ratioTest()

  val approximations = approx(value = 1.644934066848226436, base = Math.PI * Math.PI)
  println("approximations = " + approximations)
}
