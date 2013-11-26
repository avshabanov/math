#include "xmalloc.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void * xmalloc(size_t size) {
    void * p = malloc(size);
    if (p == 0) {
        fprintf(stderr, "Unable to malloc %zu block\n", size);
        abort();
    }
    return p;
}

void * xmallocz(size_t size) {
  void * p = xmalloc(size);
  memset(p, 0, size);
  return p;
}

void * xrealloc(void * p, size_t size) {
    void * result = realloc(p, size);
    if (size > 0 && result == NULL) {
        fprintf(stderr, "Unable to realloc [%p, %zu] block\n", p, size);
        abort();
    }
    return result;
}

void xfree(void * p) {
    free(p);
}
