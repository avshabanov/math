include params.mk

CC	        ?=  gcc
LINKER      ?=  gcc
CWARN       =   -Wall -Wextra -pedantic -Wno-missing-field-initializers -Wno-for-loop-analysis
CSTD        =   -std=c11
LFLAGS      =   -lm

CINCLUDE=
# optimization (O3 for max speed)
OPT= -O1
# default flags for ANSI C compilation
CFLAGS= -std=c11 ${CWARN} ${CINCLUDE} ${OPT}

.PHONY: all
all: target/rnn1 target/lstm2

#${TARGET}: prog.c Makefile ${INPUTS}
#  ${CC} ${CFLAGS} -o $@ $< $($@) ${LIBS}

target/rnn1: target/o/rnn1.o
	$(LINKER) -o target/rnn1 target/o/rnn1.o $(LFLAGS)
target/o/rnn1.o: target/o main.c
	$(CC) $(CFLAGS) $(param) $(rnn1) -c main.c -o target/o/rnn1.o

target/lstm2: target/o/lstm2.o
	$(LINKER) -o target/lstm2 target/o/lstm2.o $(LFLAGS)
target/o/lstm2.o: target/o main.c
	$(CC) $(CFLAGS) $(param) $(lstm2) -c main.c -o target/o/lstm2.o

target/o: target
	mkdir target/o

target:
	mkdir target

.PHONY: clean
clean:
	rm -rf target
