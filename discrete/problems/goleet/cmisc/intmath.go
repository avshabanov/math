package cmisc

func intGcd(a, b int) int {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func intLcm(a, b int) int {
	return a * b / intGcd(a, b)
}

func intMin(x, y int) int {
	if x < y {
		return x
	}
	return y
}

func intMax(x, y int) int {
	if x > y {
		return x
	}
	return y
}

// intAbs returns the absolute value of x.
func intAbs(x int) int {
	if x < 0 {
		return -x
	}
	return x
}
