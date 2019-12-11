#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include <strings.h>

#include "../common/invariant_check.h"

const size_t MAX_LEXEME_SIZE = 1024;
const size_t CHARS_TOTAL = 1 << CHAR_BIT;

static inline void computeStats(FILE* in, int* charStats, size_t charsTotal) {
  memset(charStats, 0, charsTotal * sizeof(int));
  for (int ch = fgetc(in); ch != EOF; ch = fgetc(in)) {
    CHECK_INVARIANT(ch >= 0 && ch < charsTotal);
    charStats[ch] = charStats[ch] + 1;
  }
}

struct {
  int ch;
  int freq;
} typedef CharFreq;

static inline int CharFreq_comparator(const void* p1, const void* p2) {
  CharFreq* lhs = (CharFreq*) p1;
  CharFreq* rhs = (CharFreq*) p2;
  return rhs->freq - lhs->freq; // sorting backwards
}

int main(int argc, char** argv) {
  fputs("Text statistics:\n", stdout);

  int charStats[CHARS_TOTAL];
  computeStats(stdin, charStats, CHARS_TOTAL);

  CharFreq frequencies[CHARS_TOTAL];
  int pos = 0;
  for (int i = 0; i < CHARS_TOTAL; ++i) {
    int st = charStats[i];
    if (st == 0) {
      continue;
    }
    CharFreq* f = &frequencies[pos];
    pos++;
    f->ch = i;
    f->freq = st;
  }

  qsort((void *) frequencies, pos, sizeof(CharFreq), CharFreq_comparator);

  for (int i = 0; i < pos; ++i) {
    CharFreq* f = &frequencies[i];
    char ch = (f->ch >= 32 ? (char) f->ch : '?');
    fprintf(stdout, "(%3d) frequency of char %c (code: %3d) is %d\n", i, ch, f->ch, f->freq);
  }

  return EXIT_SUCCESS;
}

