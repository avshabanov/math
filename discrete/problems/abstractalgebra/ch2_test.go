package abstractalgebra

import (
	"fmt"
	"strings"
	"testing"
)

// Chapter 2 Exercise C
func TestBinOpsProperties(t *testing.T) {
	// 1: Output operations
	var sb strings.Builder
	sb.WriteString(" a,b |")
	for n := 0; n < 16; n++ {
		sb.WriteString(fmt.Sprintf(" O%02d |", n))
	}
	t.Log(sb.String())
	t.Log("+----+")
	for a := 0; a <= 1; a++ {
		for b := 0; b <= 1; b++ {
			sb.Reset()
			sb.WriteString(fmt.Sprintf(" %d,%d |", a, b))
			for n := 0; n < 16; n++ {
				sb.WriteString(fmt.Sprintf("   %d |", nthBit(n, a, b)))
			}
			t.Log(sb.String())
		}
	}

	// 2, 3, 4: Check Commutativeness, Associativeness and find inverse element
	for n := 0; n < 16; n++ {
		var commutativeFlag, associativeFlag, inverseFlag string
		for a := 0; a <= 1; a++ {
			hasInverse := true
			for b := 0; b <= 1; b++ {
				// is commutative?
				if nthBit(n, a, b) != nthBit(n, b, a) {
					commutativeFlag = " not"
				}
				// is associative?
				for c := 0; c <= 1; c++ {
					if nthBit(n, a, nthBit(n, b, c)) != nthBit(n, nthBit(n, a, b), c) {
						associativeFlag = " not"
					}
				}

				// assuming a is inverse, does b*a==b holds true?
				hasInverse = hasInverse && (b == nthBit(n, b, a)) && (b == nthBit(n, a, b))
			}
			if hasInverse {
				inverseFlag = fmt.Sprintf("with inverse element %d", a)
			}
		}
		if len(inverseFlag) == 0 {
			inverseFlag = "with no inverse element"
		}

		t.Logf("O%02d is%s commutative and is%s associative and %s", n, commutativeFlag, associativeFlag, inverseFlag)
	}
}

func nthBit(num, a, b int) int {
	n := a*2 + b
	return (num & (1 << n)) >> n
}
