#pragma once

#include <stdio.h>
#include <stdlib.h>

#define CHECK_INVARIANT(cond) \
  if (!(cond)) {\
    fputs("Error: while checking invariant " #cond "\n", stderr); \
    exit(EXIT_FAILURE); \
  }
