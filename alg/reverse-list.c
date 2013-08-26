#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

struct lnode {
    int val;
    struct lnode * next;
};

struct lnode * inplace_reverse(struct lnode * start) {
    struct lnode * prev = NULL;
    while (start != NULL) {
        struct lnode * next = start->next;
        start->next = prev;
        prev = start;
        start = next;
    }
    return prev;
}

/** Creates a new node */
struct lnode * nn(int val, struct lnode * next) {
    struct lnode * n = malloc(sizeof(struct lnode));
    n->next = next;
    n->val = val;
    return n;
}

void print_list(struct lnode * n) {
    FILE * f = stdout;
    bool next = false;
    fputs("list = [", f);
    for (; n != NULL; n = n->next) {
        if (next) {
            fputs(", ", f);
        } else {
            next = true;
        }
        fprintf(f, "%d", n->val);
    }
    fputs("]\n", f);
}

int main() {
    struct lnode * n = nn(1, nn(2, nn(3, NULL)));
    print_list(n);
    n = inplace_reverse(n);
    print_list(n);
    return 0;
}


