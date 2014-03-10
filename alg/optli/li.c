// compilation: gcc -lm li.c -Wall -std=c99 -o l

#include <math.h>
#include <stdio.h>

#define GAMMA 0.57721566490153286060651209008240243104215933593992

/* floor(log2(20!)) ~ 62, log2(21!) > 65 (bits in u64) */
#define LI_D_N (20)

typedef signed int i32;
typedef signed long long i64;

/**
 * Integral logarithm from double number,
 * implementation taken from http://en.wikipedia.org/wiki/Logarithmic_integral_function
 */
double li(double x) {
  double lnx = log(x);
  i64 fn = 1; // accumulates n!
  int mo = -1; // (-1)^(n - 1)
  double lnxn = 1.0; // accumulates (ln(x)) ^ n
  double sum = 0.0;
  double ksum = 0.0;
  for (i32 n = 1; n < LI_D_N; ++n) {
    fn *= n; // n!
    mo = -mo; // (-1) ^ n
    lnxn *= lnx; // (ln(x)) ^ n
    // ((-1)^n * (ln x)^n) / (n! * 2^(n - 1))
    double m1 = mo * lnxn / (fn * (1L << (n - 1)));
    ksum += n & 1 ? (1.0 / n) : 0; // Sum{k=0}{floor((n - 1)/2)}{1/(2k + 1)}
    sum += (m1 * ksum);
    //printf("%02d: lnxn=%f, m1=%f, m2=%f, sum=%f\n", n, lnxn, m1, m2, sum);
  }
  return GAMMA + log(lnx) + sqrt(x) * sum;
}

//
// Complex arithmetics
//

/* double-based complex number */
struct complexd {
  double re;
  double im;
};

typedef struct complexd cd;

static void prn_cd(const char * name, cd * c);

static inline void mulcd(cd * acc, cd * mul) {
  double re = (acc->re * mul->re - acc->im * mul->im);
  double im = (acc->re * mul->im + acc->im * mul->re);
  acc->re = re;
  acc->im = im;
}

static inline void mulcdd(cd * acc, double d) {
  acc->re *= d;
  acc->im *= d;
}

static inline void divcdd(cd * acc, double d) {
  acc->re /= d;
  acc->im /= d;
}

static inline void addcd(cd * acc, cd * a) {
  acc->re += a->re;
  acc->im += a->im;
}

static inline void subcd(cd * acc, cd * s) {
  acc->re -= s->re;
  acc->im -= s->im;
}

static inline double modcd(cd * c) {
  return sqrt(c->re * c->re + c->im * c->im);
}

/* Square root */
static inline void sqrtcd(cd * acc) {
  double v = acc->re / 2.0;
  double u = modcd(acc) / 2;
  acc->re = sqrt(v + u);
  acc->im = (acc->im < 0.0 ? -1.0 : 1.0) * sqrt(u - v);
}

/* Complex logarithm */
static inline void logcd(cd * acc) {
  double re = log(modcd(acc));
  double im = atan2(acc->im, acc->re);
  acc->re = re;
  acc->im = im;
}

void licd(cd * x, cd * result) {
  cd lnx = *x;
  logcd(&lnx);

  i64 fn = 1; // accumulates n!
  int mo = -1; // (-1)^(n - 1)
  cd lnxn = {1.0, 0.0};
  cd sum = {0.0, 0.0};
  double ksum = 0.0;
  for (i32 n = 1; n < LI_D_N; ++n) {
    fn *= n; // n!
    mo = -mo; // (-1) ^ n
    mulcd(&lnxn, &lnx); // (ln(x)) ^ n
    // ((-1)^n * (ln x)^n) / (n! * 2^(n - 1))
    cd m1 = lnxn;
    mulcdd(&m1, mo);
    divcdd(&m1, fn * (1L << (n - 1)));
    ksum += n & 1 ? (1.0 / n) : 0; // Sum{k=0}{floor((n - 1)/2)}{1/(2k + 1)}
    mulcdd(&m1, ksum);
    addcd(&sum, &m1);
  }

  cd sqrtx = *x;
  sqrtcd(&sqrtx);
  mulcd(&sum, &sqrtx); // sum = sum * sqrt(x);

  // result = ln(ln(x))
  result->re = lnx.re; result->im = lnx.im;
  logcd(result);
  // result += GAMMA
  result->re += GAMMA;
  // result += sum;
  addcd(result, &sum);
}


static void prn_cd(const char * name, cd * c) {
  printf("%s = %f + i * %f\n", name, c->re, c->im);
}


//
// Tests
//

static inline void test_li() {
  printf("Wiki li(2) = 1.045163780117492784844588889194613136522615578151\n");
  printf("Calc li(2) = %.16f\n", li(2.0));
}

static inline void test_cd() {
  cd r = { 0.5, 1.0 }, k;
  k = r;
  prn_cd("r", &r);
  sqrtcd(&r);
  prn_cd("sqrt(r)", &r);
  r = k; logcd(&r);
  prn_cd("log(r)", &r);
  r = k;
  mulcd(&r, &r);
  prn_cd("r^2", &r);
  licd(&k, &r);
  
  printf("li(0.5 + i) = 0.485251 + 2.56262i\n");
  prn_cd("li(r)", &r);

  r.re = 10.0; r.im = 20.0;
  printf("Orig li(10 + 20i) ~ 7.886993 + 7.090242 i\n");
  licd(&r, &r);
  prn_cd("li(r)", &r);
}


int main() {
  test_li();
  test_cd();
  return 0;
}

