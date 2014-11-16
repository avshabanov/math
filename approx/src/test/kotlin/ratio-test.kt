package ratio

import org.junit.Test as test
import org.junit.Assert.*

import org.junit.Test as test

class RatioTest {

  test fun shouldReturnOne() {
    assertEquals(Ratio.ONE, Ratio(1, 1))
    assertEquals(Ratio.ONE, Ratio(2, 2))
  }

  test fun shouldCalculateGcd() {
    assertEquals(1, Ratio.gcd(3, 5))
    assertEquals(2, Ratio.gcd(16, 14))
    assertEquals(2, Ratio.gcd(14, 16))
    assertEquals(1, Ratio.gcd(73, 7))
    assertEquals(5, Ratio.gcd(45, 95))
  }

  test fun shouldBeEqualToZero() {
    assertEquals(Ratio.ZERO, Ratio(0, 111))
    assertEquals(Ratio.ZERO, Ratio(1, 2).times(Ratio(0, 1)))
    assertEquals(Ratio.ZERO, Ratio.ZERO.times(Ratio(0, 1)))
  }

  test fun shouldBeEqual() {
    assertEquals(Ratio(3, 5), Ratio(30, 50))
    assertEquals(Ratio(3, 5), Ratio(33, 55))
  }

  test fun shouldAdd() {
    assertEquals(Ratio(5, 7), Ratio(2, 7).add(Ratio(3, 7)))
    assertEquals(Ratio(14, 15), Ratio(1, 3).add(Ratio(3, 5)))
  }

  test fun shouldSubtract() {
    assertEquals(Ratio(3, 7), Ratio(5, 7).sub(Ratio(2, 7)))
    assertEquals(Ratio(1, 3), Ratio(14, 15).sub(Ratio(3, 5)))
  }

  test fun shouldMultiply() {
    assertEquals(Ratio.ZERO, Ratio(1, 2).times(Ratio.ZERO))
    assertEquals(Ratio.ONE, Ratio(1, 2).times(Ratio(2, 1)))
    assertEquals(Ratio(3, 10), Ratio(1, 2).times(Ratio(3, 5)))
    assertEquals(Ratio(63), Ratio(7).times(Ratio(9)))
  }

  test fun shouldDivide() {
    assertEquals(Ratio.ZERO, Ratio.ZERO.div(Ratio(10, 20)))
    assertEquals(Ratio.ONE, Ratio(1, 2).div(Ratio(10, 20)))
    assertEquals(Ratio.ONE, Ratio(2, 3).div(Ratio(2, 3)))
    assertEquals(Ratio(7, 15), Ratio(1, 3).div(Ratio(5, 7)))
    assertEquals(Ratio(13, 7), Ratio(13).div(Ratio(7)))
  }

  test fun shouldCopy() {
    assertEquals(Ratio(5, 7), Ratio(30, 70).copy(5))
    assertEquals(Ratio(1, 2), Ratio(4, 7).copy(denominator = 8))
  }
}
