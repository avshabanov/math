#pragma once

#include <stddef.h>

/* Fail-fast memory allocation routines */

void * xmalloc(size_t s);
void * xrealloc(void * p, size_t s);
void xfree(void * p);
