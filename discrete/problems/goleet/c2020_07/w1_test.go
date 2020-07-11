package leet

import (
	"sort"
	"testing"
)

/*
https://leetcode.com/explore/challenge/card/july-leetcoding-challenge/544/week-1-july-1st-july-7th/3383/

You are given a map in form of a two-dimensional integer grid where 1 represents land and 0 represents water.

Grid cells are connected horizontally/vertically (not diagonally). The grid is completely surrounded by water, and there is exactly one island (i.e., one or more connected land cells).

The island doesn't have "lakes" (water inside that isn't connected to the water around the island). One cell is a square with side length 1. The grid is rectangular, width and height don't exceed 100. Determine the perimeter of the island.



Example:

Input:
[[0,1,0,0],
 [1,1,1,0],
 [0,1,0,0],
 [1,1,0,0]]

Output: 16

Explanation: The perimeter is the 16 yellow stripes in the image below:
*/

func islandPerimeter(grid [][]int) int {
	// compute width and height
	height := len(grid)
	if height == 0 {
		return 0
	}
	width := len(grid[0])
	if width == 0 {
		return 0
	}

	p := 0

	for y := 0; y < height; y++ {
		for x := 0; x < width; x++ {
			if grid[y][x] == 0 {
				continue
			}

			if y == 0 || grid[y-1][x] == 0 {
				p++
			}
			if x == 0 || grid[y][x-1] == 0 {
				p++
			}
			if (y+1) == height || grid[y+1][x] == 0 {
				p++
			}
			if (x+1) == width || grid[y][x+1] == 0 {
				p++
			}
		}
	}

	return p
}

/*
https://leetcode.com/explore/challenge/card/july-leetcoding-challenge/544/week-1-july-1st-july-7th/3382/

Given a non-empty array of digits representing a non-negative integer, plus one to the integer.
The digits are stored such that the most significant digit is at the head of the list, and each element in
the array contain a single digit.
You may assume the integer does not contain any leading zero, except the number 0 itself.
*/

func plusOne(digits []int) []int {
	lastDestIndex := len(digits)
	dest := make([]int, lastDestIndex+1)
	carry := 1
	j := lastDestIndex
	for i := lastDestIndex - 1; i >= 0; i-- {
		digit := digits[i] + carry
		if digit >= 10 {
			digit -= 10
			carry = 1
		} else {
			carry = 0
		}
		dest[j] = digit
		j--
	}

	if carry > 0 {
		dest[0] = carry
		return dest
	}

	return dest[1:]
}

/*
Hamming Distance
https://leetcode.com/explore/challenge/card/july-leetcoding-challenge/544/week-1-july-1st-july-7th/3381/

The Hamming distance between two integers is the number of positions at which the corresponding bits are different.

Given two integers x and y, calculate the Hamming distance.

Note:
0 ≤ x, y < 2^31.

Example:

Input: x = 1, y = 4

Output: 2

Explanation:
1   (0 0 0 1)
4   (0 1 0 0)
       ↑   ↑

The above arrows point to positions where the corresponding bits are different.
*/

const hammingIntBits = 31

func hammingDistance(x int, y int) int {
	result := 0
	for i := 0; i < hammingIntBits; i++ {
		xb := x & 1
		yb := y & 1
		if xb != yb {
			result++
		}
		x = x >> 1
		y = y >> 1
	}
	return result
}

/*
Ugly Number II

https://leetcode.com/explore/challenge/card/july-leetcoding-challenge/544/week-1-july-1st-july-7th/3380/

Write a program to find the n-th ugly number.

Ugly numbers are positive numbers whose prime factors only include 2, 3, 5.

Example:

Input: n = 10
Output: 12
Explanation: 1, 2, 3, 4, 5, 6, 8, 9, 10, 12 is the sequence of the first 10 ugly numbers.
Note:

1 is typically treated as an ugly number.
n does not exceed 1690.
*/

func nthUglyNumber(n int) int {
	temp := sort.IntSlice{1}

	current := -1
	candidates := [3]int{}
	for i := 0; i < n; i++ {
		current = temp[0]

		candidates[0] = current * 2
		candidates[1] = current * 3
		candidates[2] = current * 5

		for j, c := range candidates {
			idx := temp.Search(c)
			if idx >= len(temp) || temp[idx] != c {
				continue
			}
			candidates[j] = -1
		}

		next := false
		for _, c := range candidates {
			if c < 0 {
				continue
			}
			if !next {
				temp[0] = c
				next = true
				continue
			}
			temp = append(temp, c)
		}

		if !next {
			panic("should never happen")
		}

		sort.Ints(temp)
	}
	return current
}

/*
Prison Cells After N Days

https://leetcode.com/explore/challenge/card/july-leetcoding-challenge/544/week-1-july-1st-july-7th/3379/

There are 8 prison cells in a row, and each cell is either occupied or vacant.

Each day, whether the cell is occupied or vacant changes according to the following rules:

If a cell has two adjacent neighbors that are both occupied or both vacant, then the cell becomes occupied.
Otherwise, it becomes vacant.
(Note that because the prison is a row, the first and the last cells in the row can't have two adjacent neighbors.)

We describe the current state of the prison in the following way: cells[i] == 1 if the i-th cell is occupied, else cells[i] == 0.

Given the initial state of the prison, return the state of the prison after N days (and N such changes described above.)

Example 1:

Input: cells = [0,1,0,1,1,0,0,1], N = 7
Output: [0,0,1,1,0,0,0,0]
Explanation:
The following table summarizes the state of the prison on each day:
Day 0: [0, 1, 0, 1, 1, 0, 0, 1]
Day 1: [0, 1, 1, 0, 0, 0, 0, 0]
Day 2: [0, 0, 0, 0, 1, 1, 1, 0]
Day 3: [0, 1, 1, 0, 0, 1, 0, 0]
Day 4: [0, 0, 0, 0, 0, 1, 0, 0]
Day 5: [0, 1, 1, 1, 0, 1, 0, 0]
Day 6: [0, 0, 1, 0, 1, 1, 0, 0]
Day 7: [0, 0, 1, 1, 0, 0, 0, 0]

Example 2:

Input: cells = [1,0,0,1,0,0,1,0], N = 1000000000
Output: [0,0,1,1,1,1,1,0]


Note:

cells.length == 8
cells[i] is in {0, 1}
1 <= N <= 10^9
*/

func prisonAfterNDaysBruteforce(cells []int, N int) []int {
	c := 0

	// fold bits
	for i := 0; i < 8; i++ {
		b := cells[i]
		c |= (b << i)
	}

	for i := 0; i < N; i++ {
		c = 0b01111110 & (^((c << 1) ^ (c >> 1)))
	}

	// unfold bits
	result := make([]int, 8)
	for i := 0; i < 8; i++ {
		b := c & 1
		c = c >> 1
		result[i] = b
	}

	return result
}

func prisonAfterNDays(cells []int, N int) []int {
	c := 0

	// fold bits
	for i := 0; i < 8; i++ {
		b := cells[i]
		c |= (b << i)
	}

	seq := make([]int, 256)
	seqPos := 0
	indices := map[int]int{}
	loopStartPos := -1
	var exists bool

	for i := 0; i < N; i++ {
		c = 0b01111110 & (^((c << 1) ^ (c >> 1)))

		var startPos int
		startPos, exists = indices[c]
		if exists {
			loopStartPos = startPos
			break
		}
		seq[seqPos] = c
		indices[c] = seqPos
		seqPos++
	}

	if loopStartPos >= 0 {
		// we didn't exhaust all the Ns, but we did find the loop
		p := N - loopStartPos - 1
		loopLen := seqPos - loopStartPos
		c = seq[loopStartPos+p%loopLen]
	}

	// unfold bits
	result := make([]int, 8)
	for i := 0; i < 8; i++ {
		b := c & 1
		c = c >> 1
		result[i] = b
	}

	return result
}

func TestCellsAfterNDays(t *testing.T) {

	//f := prisonAfterNDaysBits
	f := prisonAfterNDays

	cells := []int{0, 1, 0, 1, 1, 0, 0, 1}
	var result []int
	ns := []int{7, 0, 100, 1000, 1997, 2017, 2045, 3499}

	for _, n := range ns {
		result = prisonAfterNDaysBruteforce(append([]int{}, cells...), n)
		t.Logf("bruteforce cells(%v, %4d)=%v", cells, n, result)

		result = f(append([]int{}, cells...), n)
		t.Logf("opt        cells(%v, %4d)=%v", cells, n, result)

		t.Logf("---")
	}
}
