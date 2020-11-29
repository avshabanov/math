package simplecalc2

import "strconv"

/*
Basic Calculator II
Implement a basic calculator to evaluate a simple expression string.

The expression string contains only non-negative integers, +, -, *, / operators and empty spaces.
The integer division should truncate toward zero.

Note:
* You may assume that the given expression is always valid.
* Do not use the eval built-in library function.
*/

func calculate(s string) int {
	l := lexer{src: s}
	return evalNumOrAddSub(&l)
}

//
// implementation
//

type tokenType int

const (
	tkEOF tokenType = iota
	tkNumber
	tkPlus
	tkMinus
	tkMul
	tkDiv
)

type token struct {
	typ tokenType
	val int // for numeric tokens only
}

type lexer struct {
	stack []*token
	src   string
	pos   int
}

func (t *lexer) next() *token {
	var tok *token
	if n := len(t.stack); n > 0 {
		n--
		tok, t.stack = t.stack[n], t.stack[0:n]
		return tok
	}

	start := t.pos
	tok = &token{typ: tkEOF}
	for t.pos < len(t.src) {
		ch, pos := t.src[t.pos], t.pos
		if ch == ' ' {
			if pos == start {
				t.pos++       // move to the next character
				start = t.pos // skip leading whitespace
				continue
			}
			break // otherwise break - this is an end of lexeme
		}

		if ch >= '0' && ch <= '9' {
			tok.typ = tkNumber
			t.pos++  // move to the next character
			continue // this is a number
		}
		if tok.typ == tkNumber {
			break // we already have a number, stop parsing operand
		}
		switch ch {
		case '+':
			tok.typ = tkPlus
			break
		case '-':
			tok.typ = tkMinus
			break
		case '*':
			tok.typ = tkMul
			break
		case '/':
			tok.typ = tkDiv
			break
		default:
			panic("unexpected character")
		}
		t.pos++ // move to the next character
		break   // in either case - break as this is a singular operation
	}
	if tok.typ == tkNumber {
		var err error
		tok.val, err = strconv.Atoi(t.src[start:t.pos])
		if err != nil {
			panic("unable to convert number")
		}
	}
	return tok
}

func (t *lexer) pushBack(k *token) {
	t.stack = append(t.stack, k)
}

// Recursive-descent parser+evaluator

func evalNumOrAddSub(l *lexer) int {
	lhs := evalNumOrMulDiv(l)
	for op2 := l.next(); op2.typ != tkEOF; op2 = l.next() {
		switch op2.typ {
		case tkPlus:
			lhs += evalNumOrMulDiv(l)
		case tkMinus:
			lhs -= evalNumOrMulDiv(l)
		default:
			panic("unexpected token")
		}
	}
	return lhs
}

func evalNumOrMulDiv(l *lexer) int {
	lhs := evalNum(l)
	for op2 := l.next(); op2.typ != tkEOF; op2 = l.next() {
		switch op2.typ {
		case tkMul:
			lhs *= evalNum(l)
		case tkDiv:
			lhs /= evalNum(l)
		default:
			l.pushBack(op2)
			return lhs
		}
	}
	return lhs
}

func evalNum(l *lexer) int {
	tok := l.next()
	if tok.typ != tkNumber {
		panic("start token is not a number")
	}
	return tok.val
}
