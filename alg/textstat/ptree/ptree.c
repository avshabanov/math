#include <limits.h>

#include "ptree.h"
#include "../../common/xmalloc.h"

const size_t DEFAULT_MAX_SENTENCE_SIZE = 1024;

const size_t CHARS_TOTAL = 1 << CHAR_BIT;

typedef struct pnodeBlock pnodeBlock;

const size_t PNODE_BLOCK_SIZE = 8;

struct {

  pnodeBlock* nextLinkedBlock;
} typedef pnodeBlock;

struct {
  int textPos;
  int parentNodeIndex;
  int childrenIndices[CHARS_TOTAL];
} typedef pnode;

struct Ptree {
  struct {
    size_t maxSentenceSize;
  } settings;
  size_t nodesCount;
  size_t bufSize;
  size_t hits;
  char buf[1];
};

struct PtreeSettings defaultSettings = {
  100000,
};

struct Ptree* Ptree_new(struct PtreeSettings* s) {
  s = (s == NULL ? &defaultSettings : s);
  struct Ptree* pt = xmallocz(sizeof(struct Ptree) + s->bufSize - 1);
  pt->bufSize = s->bufSize;

  // TODO: move this to settings
  pt->settings.maxSentenceSize = DEFAULT_MAX_SENTENCE_SIZE;
  return pt;
}

void Ptree_feedSentence(struct Ptree* pt, FILE* in, size_t limit) {
  // here: sentence ends when either MAX_SENTENCE_SIZE limit is reached or dot found

}

void Ptree_free(struct Ptree* pt) {
  pt->bufSize = 0;
  xfree(pt);
}
