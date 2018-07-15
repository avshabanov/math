include target/config.mk

CC			=		gcc
LINKER	=		gcc

CFLAGS	+=	-std=c++11 -Wall -pedantic
LFLAGS	+=  -lstdc++

.PHONY: all
all: target/ublas-net

target/ublas-net: target/o/main.o target/o/net.o
	$(LINKER) -o target/ublas-net target/o/*.o $(LFLAGS)

target/o/main.o: target/o main.cpp net.h
	$(CC) $(CFLAGS) -c main.cpp -o target/o/main.o

target/o/net.o: target/o net.cpp net.h
	$(CC) $(CFLAGS) -c net.cpp -o target/o/net.o

target/o:
	mkdir -p target/o

