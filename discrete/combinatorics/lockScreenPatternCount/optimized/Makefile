
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

target/classes/LockScreenPatternCountOptExample.class: target/classes LockScreenPatternCountOptExample.java
	javac -d target/classes LockScreenPatternCountOptExample.java

compile: target/classes/LockScreenPatternCountOptExample.class

run:
	java -XX:+AggressiveOpts -cp target/classes optimized.LockScreenPatternCountOptExample

clean:
	rm -rf target

