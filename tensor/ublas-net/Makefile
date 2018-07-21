include target/config.mk

CC			=		gcc
LINKER	=		gcc

CFLAGS	+=	-std=c++11 -Wall -pedantic
LFLAGS	+=  -lstdc++

LFLAGS_TEST = $(LFLAGS) -lboost_unit_test_framework

CFLAGS	+=	-DUBLASNET_DEBUG

OBJ			=		target/o
OBJ_FILES =		$(OBJ)/net.o $(OBJ)/netmeta.o

.PHONY: all
all: target/ublas-net

target/ublas-net: $(OBJ)/main.o $(OBJ_FILES)
	$(LINKER) -o target/ublas-net $(OBJ_FILES) $(OBJ)/main.o $(LFLAGS)

$(OBJ)/main.o: $(OBJ) src/main.cpp src/net.h src/utils/matrix_utils.h
	$(CC) $(CFLAGS) -c src/main.cpp -o $(OBJ)/main.o

$(OBJ)/net.o: $(OBJ) src/net.cpp src/net.h src/utils/matrix_utils.h
	$(CC) $(CFLAGS) -c src/net.cpp -o $(OBJ)/net.o

$(OBJ)/netmeta.o: $(OBJ) src/netmeta.cpp src/net.h
	$(CC) $(CFLAGS) -c src/netmeta.cpp -o $(OBJ)/netmeta.o

$(OBJ):
	mkdir -p $(OBJ)

.PHONY: test
test: ./target/run-net-test
	./target/run-net-test

./target/run-net-test: $(OBJ)/net_test.o $(OBJ_FILES)
	$(LINKER) -o ./target/run-net-test $(OBJ)/net_test.o $(OBJ_FILES) $(LFLAGS_TEST)

$(OBJ)/net_test.o: $(OBJ) src/net_test.cpp src/net.h src/utils/matrix_utils.h
	$(CC) $(CFLAGS) -c src/net_test.cpp -o $(OBJ)/net_test.o

.PHONY: clean
clean:
	rm -rf target