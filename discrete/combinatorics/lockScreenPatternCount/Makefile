
# Run `make` to compile
# Run `make clean` to clean target folder
# Run `make run` to run compiled program


.PHONY: clean compile run

#
# Targets
#

all: compile

target:
	mkdir target

target/classes: target
	mkdir target/classes

target/classes/LockScreenPatternCountAdvExample.class: target/classes LockScreenPatternCountAdvExample.java
	javac -d target/classes LockScreenPatternCountAdvExample.java

compile: target/classes/LockScreenPatternCountAdvExample.class

run:
	java -XX:+AggressiveOpts -cp target/classes LockScreenPatternCountAdvExample

clean:
	rm -rf target

