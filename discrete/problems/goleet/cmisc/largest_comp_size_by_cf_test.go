package cmisc

import (
	"testing"
)

type factorChain struct {
	parent []int
}

func (d *factorChain) find(x int) int {
	if d.parent[x] != x {
		d.parent[x] = d.find(d.parent[x])
	}
	return d.parent[x]
}

func (d *factorChain) union(x, y int) {
	d.parent[d.find(x)] = d.parent[d.find(y)]
}

func newFactorChain(n int) *factorChain {
	s := make([]int, n)
	for i := 0; i < n; i++ {
		s[i] = i
	}
	return &factorChain{s}
}

func largestComponentSize2(arr []int) int {
	ans, max, cache := 1, 0, make(map[int]int)
	for _, a := range arr {
		if a > max {
			max = a
		}
	}
	chain := newFactorChain(max + 1)
	for _, a := range arr {
		for k := 2; k*k <= a; k++ {
			if a%k == 0 {
				chain.union(a, k)
				chain.union(a, a/k)
			}
		}
	}
	for _, a := range arr {
		r := chain.find(a)
		cache[r]++
		if cache[r] > ans {
			ans = cache[r]
		}
	}
	return ans
}

func TestLargestComponentSize320(t *testing.T) {
	//n := largestComponentSize([]int{2, 2 * 3, 7, 7 * 5, 2 * 5, 11, 17})
	n := largestComponentSize2([]int{2, 3, 6, 7, 4, 12, 21, 39})
	t.Logf("[1] n=%d", n)
}
