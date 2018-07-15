include target/config.mk

CC			=		gcc
LINKER	=		gcc

CFLAGS	+=	-std=c++11 -Wall -pedantic
LFLAGS	+=  -lstdc++

.PHONY: all
all: target/ublas-net

target/ublas-net: target/o/main.o
	$(LINKER) -o target/ublas-net target/o/main.o $(LFLAGS)

target/o/main.o: target/o main.cpp
	$(CC) $(CFLAGS) -c main.cpp -o target/o/main.o

target/o:
	mkdir -p target/o

