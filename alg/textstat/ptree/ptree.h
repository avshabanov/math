#pragma once

#include <stdio.h>

struct PtreeSettings {
  size_t bufSize;
};

struct Ptree;

struct Ptree* Ptree_new(struct PtreeSettings* s);
void Ptree_free(struct Ptree* pt);
