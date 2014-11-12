package approx.basel

import java.util.ArrayList
import java.math.BigDecimal
import java.math.BigInteger
import java.util.HashSet

data class Ratio private (val numerator : Int, val denominator : Int) {
  class object {
    fun create(numerator : Int, denominator : Int) : Ratio {
      val gcd = BigInteger.valueOf(numerator.toLong()).gcd(BigInteger.valueOf(denominator.toLong())).intValue();
      return Ratio(numerator / gcd, denominator / gcd)
    }
  }
}

fun approx(value : Double, base : Double, epsilon : Double = 0.000001, ratioLim : Int = 10000) : Collection<Ratio> {
  val result = HashSet<Ratio>()
  for (denom in 1..ratioLim) {
    for (num in 1..ratioLim) {
      val x = base * num / denom
      if (x > value) {
        break
      } else if (Math.abs(value - x) < epsilon) {
        result.add(Ratio.create(numerator = num, denominator = denom))
      }
    }
  }
  return result
}

fun main(args: Array<String>) {
  val approximations = approx(value = 1.644934066848226436, base = Math.PI * Math.PI)
  println("approximations = " + approximations)
}
