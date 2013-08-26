/* The Computer Language Benchmarks Game
 * http://benchmarksgame.alioth.debian.org/

 * Contributed by Joern Inge Vestgaarden
 * Modified by Jorge Peixoto de Morais Neto
 * Modified by Alexander Shabanov
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <err.h>

#if 1
#define fwrite_unlocked fwrite
#define fputs_unlocked fputs
#define putchar_unlocked putchar
#endif

#define WIDTH 60
#define MIN(a,b) ((a) <= (b) ? (a) : (b))
#define NELEMENTS(x) (sizeof (x) / sizeof ((x)[0]))

/* num(numerator) / den (denumerator) */
typedef struct {
    long num;
    long den;
} ratio_t;

static inline void ratio_inc(ratio_t * accum, ratio_t * delta) {
    if (accum->num == 0) {
	accum->num = delta->num;
	accum->den = delta->den;
    } else if (accum->den == delta->den) {
	accum->num += delta->num;
    } else {
	/* TODO: find common divisors and shorten ratio to not to run out of long space */
	accum->num = accum->num * delta->den + delta->num * accum->den;
	accum->den = accum->den * delta->den;
    }
}

static inline void ratio_set(ratio_t * lval, ratio_t * rval) {
    lval->num = rval->num;
    lval->den = rval->den;
}

static inline long ratio_less(ratio_t * lhs, ratio_t * rhs) {
    return lhs->num * rhs->den - rhs->num * lhs->den;
}

typedef struct {
    ratio_t p;
    //float p;
    char c;
} aminoacid_t;

/* ratio_1 == 1 or 1.0 */
static ratio_t ratio_1 = { 1, 1 };

/* calculates random not exceeding the max */
static inline void ratio_gene_rand(ratio_t * max, ratio_t * result) {
    unsigned long const IM = 139968;
    unsigned long const IA = 3877;
    unsigned long const IC = 29573;
    static long last = 42;
    last = (last * IA + IC) % IM;
    result->num = max->num * last;
    result->den = max->den * IM;
}

static inline void accumulate_probabilities (aminoacid_t *genelist, size_t len) {
    ratio_t cp = { 0, 0 };
    size_t i;
    for (i = 0; i < len; i++) {
	ratio_inc(&cp, &genelist[i].p);
	ratio_set(&genelist[i].p, &cp);
    }
}

/* This function prints the characters of the string s. When it */
/* reaches the end of the string, it goes back to the beginning */
/* It stops when the total number of characters printed is count. */
/* Between each WIDTH consecutive characters it prints a newline */
/* This function assumes that WIDTH <= strlen (s) + 1 */
static void repeat_fasta (char const *s, size_t count) {
    size_t pos = 0;  
    size_t len = strlen (s); 
    char *s2 = malloc (len + WIDTH);
    memcpy (s2, s, len); 
    memcpy (s2 + len, s, WIDTH); 
    do {   
     	size_t line = MIN(WIDTH, count); 
     	fwrite_unlocked (s2 + pos,1,line,stdout); 
     	putchar_unlocked ('\n'); 
     	pos += line; 
     	if (pos >= len) pos -= len; 
     	count -= line;  
    } while (count); 
    free (s2);
}

/* This function takes a pointer to the first element of an array */
/* Each element of the array is a struct with a character and */
/* a float number p between 0 and 1. */
/* The function generates a random float number r and */
/* finds the first array element such that p >= r. */
/* This is a weighted random selection. */
/* The function then prints the character of the array element. */
/* This is done count times. */
/* Between each WIDTH consecutive characters, the function prints a newline */
static void random_fasta (aminoacid_t * genelist, size_t count) {
    do {    
	size_t line = MIN(WIDTH, count);    
	size_t pos = 0;    
	char buf[WIDTH + 1];    
	do {
	    ratio_t r;
	    ratio_gene_rand(&ratio_1, &r);
	    size_t i = 0;   
	    while (ratio_less(&genelist[i].p, &r) < 0) {
		++i; /* Linear search */
	    }    
	    buf[pos++] = genelist[i].c;    
	} while (pos < line);   
	buf[line] = '\n';
	fwrite_unlocked (buf, 1, line + 1, stdout);    
	count -= line;    
    } while (count);   
}

int main (int argc, char **argv) {
    size_t n;
    if (argc > 1) { 
	char const *arg = argv[1];
 	char *tail; 
 	n = strtoul (arg, &tail, 0); 
 	if (tail == arg)  
	    errx (1, "Could not convert \"%s\" to an unsigned long integer", arg); 
    } else {
	n = 1000;
    }

    static aminoacid_t iub[] = {
	{ { 27, 100 }, 'a' },
	{ { 3, 25 }, 'c' },
	{ { 3, 25 }, 'g' },
	{ { 27, 100 }, 't' },
	{ { 1, 50 }, 'B' },
	{ { 1, 50 }, 'D' },
	{ { 1, 50 }, 'H' },
	{ { 1, 50 }, 'K' },
	{ { 1, 50 }, 'M' },
	{ { 1, 50 }, 'N' },
	{ { 1, 50 }, 'R' },
	{ { 1, 50 }, 'S' },
	{ { 1, 50 }, 'V' },
	{ { 1, 50 }, 'W' },
	{ { 1, 50 }, 'Y' }};

    static aminoacid_t homosapiens[] = {
	{ { 3029549426680L, 10000000000000L }, 'a' },
	{ { 1979883004921L, 10000000000000L }, 'c' },
	{ { 1975473066391L, 10000000000000L }, 'g' },
	{ { 3015094502008L, 10000000000000L }, 't' }};

    accumulate_probabilities (iub, NELEMENTS(iub)); 
    accumulate_probabilities (homosapiens, NELEMENTS(homosapiens));

    static char const *const alu ="\
GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGG\
GAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGA\
CCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAAT\
ACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCA\
GCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGG\
AGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCC\
AGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA";

    fputs_unlocked (">ONE Homo sapiens alu\n", stdout);
    repeat_fasta (alu, 2 * n);
    fputs_unlocked (">TWO IUB ambiguity codes\n", stdout);
    random_fasta (iub, 3 * n);
    fputs_unlocked (">THREE Homo sapiens frequency\n", stdout);
    random_fasta (homosapiens, 5 * n);
    return 0;
}
