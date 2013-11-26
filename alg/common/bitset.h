#pragma once
#include <limits.h>
#include <assert.h>
#include <stdio.h>

struct bitset_t {
  unsigned long * buf;
  size_t bit_count;
};

#define ULONG_BITS    (CHAR_BIT * sizeof(unsigned long))


struct bitset_t * bitset_alloc(size_t bit_count);

void bitset_free(struct bitset_t * bitset);

static inline void bitset_set_bit(struct bitset_t * bitset, size_t bit_pos) {
  assert(bit_pos < bitset->bit_count);
  bitset->buf[bit_pos / ULONG_BITS] |= (1UL << (bit_pos % ULONG_BITS));
}

static inline void bitset_reset_bit(struct bitset_t * bitset, size_t bit_pos) {
  assert(bit_pos < bitset->bit_count);
  bitset->buf[bit_pos / ULONG_BITS] &= ~(1UL << (bit_pos % ULONG_BITS));
}

static inline unsigned int bitset_get_bit(struct bitset_t * bitset, size_t bit_pos) {
  assert(bit_pos < bitset->bit_count);
  return (bitset->buf[bit_pos / ULONG_BITS] & (1UL << (bit_pos % ULONG_BITS))) > 0;
}

void bitset_print(struct bitset_t * bitset, FILE * out);

