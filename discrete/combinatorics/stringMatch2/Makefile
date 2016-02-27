
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

target/classes/StringMatch2Example.class: target/classes StringMatch2Example.java
	javac -d target/classes StringMatch2Example.java

compile: target/classes/StringMatch2Example.class

run:
	java -cp target/classes StringMatch2Example

clean:
	rm -rf target

