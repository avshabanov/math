/*
 * Compile and start:
 * gcc -Icommon -Wall -O1 primes/main.c common/xmalloc.c common/bitset.c -o primes.out; ./primes.out 0 100000
 *
 * Verify at wolframalpha.com
 *  pi(1000) = 168
 *  pi(10000) = 1229
 *  pi(100000) = 9592
 *
 *  pi(1000000000) = 50847534
 */

#include <bitset.h>

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

struct primes_sieve_context_t {
  struct bitset_t * sieve;
  size_t prime_count;
};

void prime_sieve_context_dtor(struct primes_sieve_context_t * c) {
  if (c->sieve) {
    bitset_free(c->sieve);
  }
}

static void gen_primes_sieve(size_t from, size_t to, struct primes_sieve_context_t * c) {
  struct bitset_t * s = bitset_alloc(to);
  c->sieve = s;
  c->prime_count = 0;
  bitset_set_bit(s, 0);
  bitset_set_bit(s, 1);

  /* fill Erathosphen sieve */
  for (size_t i = 0; i < to; ++i) {
    if (!bitset_get_bit(s, i)) {
      for (size_t j = i * i; j < to; j += i) {
        bitset_set_bit(s, j);
      }
    }
  }

  /* count numbers */
  for (size_t i = from; i < to; ++i) {
    if (!bitset_get_bit(s, i)) {
      ++c->prime_count;
    }
  }
}


int main(int argc, char * argv[]) {
  long from = 0;
  long to = 20;
  int print_bitset = 1;
  struct primes_sieve_context_t psc;

  if (argc < 3) {
    fputs("No arguments, proceeding with default values.\n"
        "Usage: primes {from} {to} {0,1: print_bitset}\n", stderr);
  } else {
    from = atol(argv[1]);
    if (errno == EINVAL || from < 0) {
      fputs("First arg is not a positive number", stderr);
      abort();
    }
    to = atol(argv[2]);
    if (errno == EINVAL || to < 0) {
      fputs("Second arg is not a positive number", stderr);
      abort();
    }
    print_bitset = argc > 3 ? atoi(argv[3]) : 0;
  }

  gen_primes_sieve((size_t) from, (size_t) to, &psc);
  printf("Count of primes in [%ld, %ld) = %zu\n", from, to, psc.prime_count);
  if (print_bitset) {
    printf("Bitset = ");
    bitset_print(psc.sieve, stdout);
  }
  printf("\n");
  
  prime_sieve_context_dtor(&psc);
  return 0;
}

