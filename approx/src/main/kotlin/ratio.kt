package ratio

/**
 * An abstraction over rational number, i.e. number which is represented as a ratio of an integer numerator
 * to integer non-zero denominator.
 */
class Ratio private (val numerator : Int, val denominator : Int) {
  class object {
    val ZERO = Ratio(0, 1)
    val ONE = Ratio(1, 1)

    fun invoke(numerator : Int = 1, denominator : Int = 1) : Ratio {
      if (denominator == 0) {
        throw IllegalArgumentException("denominator can't be zero")
      }
      if (numerator == 0) {
        return ZERO
      }
      if (numerator == denominator) {
        return ONE
      }

      val d = gcd(numerator, denominator)
      return Ratio(numerator / d, denominator / d)
    }

    fun gcd(a : Int, b : Int) : Int {
      if (a == 0) {
        return b
      } else if (b == 0) {
        return a
      } else if (a == b) {
        return a
      } else if (a > b) {
        return gcd(a - b, b)
      } else {
        return gcd(a, b - a)
      }
    }
  }

  // this enables clients to write `a * b` for two ratios
  fun times(other: Ratio) = invoke(this.numerator * other.numerator, this.denominator * other.denominator)

  // a / b
  fun div(other : Ratio) = invoke(this.numerator * other.denominator, this.denominator * other.numerator)

  // a + b
  fun add(other : Ratio) = invoke(this.numerator * other.denominator + this.denominator * other.numerator,
      this.denominator * other.denominator)

  // a - b
  fun sub(other : Ratio) = invoke(this.numerator * other.denominator - this.denominator * other.numerator,
      this.denominator * other.denominator)

  fun copy(numerator: Int? = null, denominator: Int? = null): Ratio = invoke(numerator ?: this.numerator,
      denominator ?: this.denominator)

  override fun equals(other: Any?) : Boolean {
    if (other is Ratio) {
      return this.numerator == other.numerator && this.denominator == other.denominator
    }
    return false
  }

  override fun hashCode() : Int {
    return this.numerator * 31 + this.denominator
  }

  // custom toString(), the automatically generated one would be giving "Ratio(numerator=2, denominator=3)"
  override fun toString() = "$numerator/$denominator"
}

