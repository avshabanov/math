
/* Represents simple ring buffer */

#include "common/xmalloc.h"

#include <string.h>
#include <stdbool.h>

/*
 * Compile as follows for test:
 * gcc -g -Wall -std=c99 -DRINGBUF_TEST=1 ring-buffer.c common/xmalloc.c -o rb
 */

#if defined(RINGBUF_TEST) && RINGBUF_TEST
#include <stdio.h>
#include <stdlib.h>
#endif

/* = Reusable part = */

/**
 * Element type
 */
typedef int ringbuf_elem_t;



/* = Implementation = */

struct ringbuf {
    size_t capacity; /* Overall capacity minus one empty element */
    size_t start_index; /* Index of the first element in the buffer */
    size_t end_index; /* Index of the element after the last in the buffer */
    ringbuf_elem_t * elements;
};

struct ringbuf * ringbuf_alloc(size_t capacity) {
    struct ringbuf * s = xmalloc(sizeof(struct ringbuf));
    // TODO: if capacity+1 was a power of 2 it may work much faster
    // capacity + 1 (empty) element
    s->capacity = capacity + 1;
    s->elements = xmalloc(s->capacity * sizeof(ringbuf_elem_t));
    s->start_index = 0;
    s->end_index = 0;
    return s;
}

void ringbuf_free(struct ringbuf * s) {
    xfree(s->elements);
    xfree(s);
}

bool ringbuf_is_empty(struct ringbuf * s) {
    return s->start_index == s->end_index;
}

bool ringbuf_is_full(struct ringbuf * s) {
    // TODO: if capacity was a power of 2 it may work much faster
    return s->start_index == ((s->end_index + 1) % s->capacity);
}

size_t ringbuf_size(struct ringbuf * s) {
    // TODO: if capacity was a power of 2 it may work much faster
    return (s->capacity + s->end_index - s->start_index) % s->capacity;
}

/**
 * Inserts new element at the back of the buffer, 
 * returns 0 on succeed, -1 otherwise
 */
bool ringbuf_push_back(struct ringbuf * s, ringbuf_elem_t e) {
    // TODO: if capacity was a power of 2 it may work much faster
    size_t new_end_index = (s->end_index + 1) % s->capacity;
    if (new_end_index == s->start_index) {
        return false;
    }

    s->elements[s->end_index] = e; // TODO: generalized set
    s->end_index = new_end_index;
    return true;
}

bool ringbuf_pop_front(struct ringbuf * s, ringbuf_elem_t * er) {
    size_t new_start_index = (s->start_index + 1) % s->capacity;
    if (new_start_index > s->end_index) {
        return false;
    }
    *er = s->elements[s->start_index]; // TODO: generalized set
    s->start_index = new_start_index;
    return true;
}

bool ringbuf_at(struct ringbuf * s, size_t pos, ringbuf_elem_t * er) {
    size_t index;
    if (pos >= s->capacity) {
        return false;
    }
    index = (s->start_index + pos) % s->capacity;
    if (index < s->start_index && index >= s->end_index) {
        return false;
    }
    *er = s->elements[index]; // TODO: generalized set
    return true;
}

/*
 * Test code
 */

#if defined(RINGBUF_TEST) && RINGBUF_TEST

static void pop_and_prn_ringbuf(struct ringbuf * s) {
    int e = -1;
    bool got = ringbuf_pop_front(s, &e);
    fprintf(stdout, "got=%d, elem=%d, is_empty=%d, is_full=%d, size=%zu\n",
            got, e, ringbuf_is_empty(s), ringbuf_is_full(s), ringbuf_size(s));
}

static void prn_ringbuf(struct ringbuf * s) {
    FILE * f = stdout;
    size_t size = ringbuf_size(s);
    size_t i;
    fputs("ringbuf = [", f);
    for (i = 0; i < size; ++i) {
        int e = -1;
        if (i > 0) {
            fputs(", ", f);
        }
        if (!ringbuf_at(s, i, &e)) {
            fprintf(stderr, "FATAL: Error reading from ringbuf!\n");
            abort();
        }
        fprintf(f, "%d", e);
    }
    fprintf(f, "], is_empty=%d, is_full=%d, size=%zu\n", 
            ringbuf_is_empty(s), ringbuf_is_full(s), size);
}

int main() {
    struct ringbuf * s;
    s = ringbuf_alloc(3);
    prn_ringbuf(s);

    ringbuf_push_back(s, 1); prn_ringbuf(s);
    ringbuf_push_back(s, 2); prn_ringbuf(s);
    ringbuf_push_back(s, 3); prn_ringbuf(s);
    ringbuf_push_back(s, -300); prn_ringbuf(s);
    fputs("============\n", stdout);

    pop_and_prn_ringbuf(s);
    pop_and_prn_ringbuf(s); prn_ringbuf(s);
    ringbuf_push_back(s, 4); prn_ringbuf(s);
    ringbuf_push_back(s, 5); prn_ringbuf(s);

    ringbuf_free(s);
    return 0;
}

#endif /* RINGBUF_TEST */
