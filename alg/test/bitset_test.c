/*
 * gcc -Icommon -Wall -O1 test/bitset_test.c common/xmalloc.c common/bitset.c -o bitset_test.out 
 */


#include "bitset.h"

int main(int argc, char * argv[]) {
  struct bitset_t * b = bitset_alloc(65);
  bitset_set_bit(b, 0);
  bitset_set_bit(b, 5);
  bitset_set_bit(b, 3);
  bitset_set_bit(b, 10);
  bitset_set_bit(b, 59);
  bitset_reset_bit(b, 10);
  fprintf(stdout, "bitset = ");
  bitset_print(b, stdout);
  fputs("\n", stdout);
  return 0;
}

