#include <cstdio>
#include <cstdint>

#include <stdexcept>

#define DBG   (1)

class half {
  uint16_t n;

  // IEEE 754 float spec
  static const size_t BIT_FLOAT_FRAC = 23;
  static const size_t BIT_FLOAT_SIGN = 31;
  static const uint32_t FLOAT_SIGN_MASK = 1 << BIT_FLOAT_SIGN;

  // IEEE 754 half-precision set
  static const size_t BIT_HALF_FRAC = 11;
  static const size_t BIT_HALF_SIGN = 15;
  static const uint16_t HALF_SIGN_MASK = 1 << BIT_HALF_SIGN;

  static const int32_t MAX_HALF_EXP = (1 << (BIT_HALF_SIGN - BIT_HALF_FRAC)) - 1;
  // Defines difference between exponent base
  static const int32_t FLOAT_TO_HALF_EXP_DIFF = (1 << (BIT_FLOAT_SIGN - BIT_FLOAT_FRAC - 1)) - (1 << (BIT_HALF_SIGN - BIT_HALF_FRAC - 1));
public:
  half(uint16_t raw) : n(raw) {}

  half(float v) {
    uint32_t p = *((uint32_t *) &v);
    uint32_t pu = p & (FLOAT_SIGN_MASK - 1);
    uint32_t exp32 = pu >> BIT_FLOAT_FRAC;
    int32_t exp16 = exp32 - FLOAT_TO_HALF_EXP_DIFF;
    if (exp16 < 0 || exp16 > MAX_HALF_EXP) {
      throw std::logic_error("exponent is out of range"); // check overflow
    }
    
    uint32_t frac = (p >> (BIT_FLOAT_FRAC - BIT_HALF_FRAC)) & ((1 << BIT_HALF_FRAC) - 1);

#ifdef DBG
    printf(" [DBG] Pack: v=%.4f, p=0x%04x, exp16=%d, exp32=%d, frac=0x%x\n", v, p, exp16, exp32, frac);
#endif
    
    uint32_t nt = (p & FLOAT_SIGN_MASK) >> (BIT_FLOAT_SIGN - BIT_HALF_SIGN);
    nt |= frac;
    nt |= (exp16 << BIT_HALF_FRAC);
    n = (uint16_t) nt;
  }

  void operator = (half v) { n = v.n; }

  float to_float() const {
    uint32_t frac = n & ((1 << BIT_HALF_FRAC) - 1);
    uint32_t exp16 = (n & (~HALF_SIGN_MASK)) >> BIT_HALF_FRAC;
    uint32_t exp32 = FLOAT_TO_HALF_EXP_DIFF + exp16;

    // join all components: sign, exponent and fractional parts
    uint32_t r = ((n & HALF_SIGN_MASK) << (BIT_FLOAT_SIGN - BIT_HALF_SIGN)) |
      (exp32 << BIT_FLOAT_FRAC) |
      (frac << (BIT_FLOAT_FRAC - BIT_HALF_FRAC));

#ifdef DBG
    printf(" [DBG] Unpack: n=0x%x, frac=0x%x, exp16=%d, expr32=%d, r=0x%08x\n", n, frac, exp16, exp32, r);
#endif

    // transfer joined components to float variable
    float f;
    *((uint32_t *) &f) = r;

    return f;
  }

  uint16_t raw() const { return n; }
};

int main() {
  puts("half float demo\n");
  float nums[] = {1.0f, 0.5f, -0.5f, -3.5f, 10.725f};

  for (auto f : nums) {
    half h(f);
    float fa = h.to_float();
     printf(" > f = %.3f, fa = %.3f, ha.raw()=%02x\n", f, fa, h.raw());
  }

  return 0;
}

