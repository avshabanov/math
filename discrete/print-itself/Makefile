
CC			?=	gcc
CFLAGS	?=	-std=c99 -Wall -O1

LINKER	?=	gcc
LFLAGS	?=

.PHONY: all
all: target/print-all

target/print-all: target/o/main.o
	$(LINKER) -o target/print-all target/o/main.o $(LFLAGS)

target/o/main.o: target/o main.c
	$(CC) $(CFLAGS) -c main.c -o target/o/main.o

# Object files
target/o: target
	mkdir target/o

target:
	mkdir target

.PHONY: clean
clean:
	rm -rf target
