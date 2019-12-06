#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include <strings.h>

const size_t MAX_LEXEME_SIZE = 1024;
const size_t CHARS_TOTAL = 1 << CHAR_BIT;
int CHAR_STATS[CHARS_TOTAL];

int main(int argc, char** argv) {
  fputs("Text statistics\n", stdout);
  FILE *in = stdin;

  memset(CHAR_STATS, 0, sizeof(CHAR_STATS));

  char lexeme[MAX_LEXEME_SIZE];
  for (;;) {
    int ch = fgetc(in);
    if (ch == EOF) {
      break;
    }

    // increment char statistics
    CHAR_STATS[ch] = CHAR_STATS[ch] + 1;
  }

  for (int i = 0; i < CHARS_TOTAL; ++i) {
    int st = CHAR_STATS[i];
    if (st == 0) {
      continue;
    }
    char ch = (i >= 32) ? (char) i : '?';
    fprintf(stdout, "Char %3d (%c) stat: %d\n", i, ch, st);
  }

  return EXIT_SUCCESS;
}
