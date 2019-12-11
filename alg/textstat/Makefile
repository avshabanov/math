
CC			?=	gcc
CFLAGS	?=	-std=c99 -Wall -O1

LINKER	?=	gcc
LFLAGS	?=

.PHONY: all
all: target/textstat

target/textstat: target/o/textstat.o
	$(LINKER) -o target/textstat target/o/textstat.o $(LFLAGS)

target/o/textstat.o: target/o textstat.c
	$(CC) $(CFLAGS) -c textstat.c -o target/o/textstat.o

# Object files
target/o: target
	mkdir target/o

target:
	mkdir target

.PHONY: clean
clean:
	rm -rf target
