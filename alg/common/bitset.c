#include "bitset.h"
#include "xmalloc.h"

#include <string.h>

struct bitset_t * bitset_alloc(size_t bit_count) {
  struct bitset_t * r = xmalloc(sizeof(struct bitset_t));
  size_t buf_size = bit_count / ULONG_BITS + (bit_count % ULONG_BITS > 0 ? 1: 0);
  r->bit_count = bit_count;
  r->buf = xmallocz(sizeof(unsigned long) * buf_size);
  return r;
}

void bitset_free(struct bitset_t * bitset) {
  xfree(bitset->buf);
  xfree(bitset);
}

static inline char bit_to_char(unsigned int b) {
  switch (b) {
    case 0:
      return '.';
    case 1:
      return '1';
    default:
      return '?';
  }
}

void bitset_print(struct bitset_t * bitset, FILE * out) {
  size_t i;
  fputs("#*(", out);
  for (i = 0; i < bitset->bit_count; ++i) {
    fputc(bit_to_char(bitset_get_bit(bitset, i)), out);
  }
  fputc(')', out);
}

