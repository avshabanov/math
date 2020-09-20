package miscleetproblems

import (
	"fmt"
	"math"
	"math/bits"
	"math/rand"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"testing"
)

func TestSample(t *testing.T) {
	t.Logf("result=%d", rand.Intn(10))
}

/*
Unique Paths III
On a 2-dimensional grid, there are 4 types of squares:

1 represents the starting square.  There is exactly one starting square.
2 represents the ending square.  There is exactly one ending square.
0 represents empty squares we can walk over.
-1 represents obstacles that we cannot walk over.
Return the number of 4-directional walks from the starting square to the ending square, that walk over every
non-obstacle square exactly once.

1 <= grid.length * grid[0].length <= 20
*/

func uniquePathsIII(grid [][]int) int {
	if len(grid) == 0 || len(grid[0]) == 0 {
		return 0 // empty grid
	}
	t := uniquePaths3Iterator{grid: grid, width: len(grid[0]), height: len(grid)}

	startx, starty := -1, -1

	// find start square and count of passable squares
	for y := 0; y < t.height; y++ {
		for x := 0; x < t.width; x++ {
			switch grid[y][x] {
			case 1:
				startx, starty = x, y   // found start square
				t.passableSquareCount++ // initial square IS passable
			case 0:
				t.passableSquareCount++ // 0-square is passable too
			}
		}
	}

	t.iter(startx, starty)

	return t.result
}

type uniquePaths3Iterator struct {
	grid                [][]int
	width               int
	height              int
	passableSquareCount int
	result              int
}

func (t *uniquePaths3Iterator) iter(x, y int) {
	if x < 0 || x >= t.width || y < 0 || y >= t.height {
		return
	}

	square := t.grid[y][x]
	switch square {
	case 2:
		if t.passableSquareCount == 0 {
			t.result++ // found a destination
		}
		return
	case -1:
		return // impassable
	default: // fall through
	}

	t.grid[y][x] = -1       // mark this square as impassable
	t.passableSquareCount-- // decrement number of passable squares as we mark this one as occupied
	t.iter(x-1, y)
	t.iter(x, y-1)
	t.iter(x+1, y)
	t.iter(x, y+1)
	t.passableSquareCount++ // restore number of passable squares
	t.grid[y][x] = square   // restore square
}

/*
Sequential Digits
An integer has sequential digits if and only if each digit in the number is one more than the previous digit.

Return a sorted list of all the integers in the range [low, high] inclusive that have sequential digits.
*/

func sequentialDigits(low int, high int) []int {
	dit := digitsIterator{low: low, high: high, digits: make([]int, 10)}
	dit.inc(0)
	sort.Ints(dit.sink)
	return dit.sink
}

type digitsIterator struct {
	sink        []int
	digits      []int
	composedNum int
	low         int
	high        int
}

func (t *digitsIterator) inc(pos int) {
	if pos == 0 {
		for i := 1; i <= 8; i++ {
			t.composedNum = i
			t.digits[0] = i
			t.inc(1)
		}
		return
	}

	prev := t.digits[pos-1]
	if prev == 9 {
		return
	}

	prevComposedNum := t.composedNum
	newDigit := prev + 1
	t.digits[pos] = newDigit
	t.composedNum = prevComposedNum*10 + newDigit
	if t.composedNum < t.low {
		t.inc(pos + 1)
	} else if t.composedNum <= t.high {
		// this number is actually within the permitted bounds, include it
		t.sink = append(t.sink, t.composedNum)
		t.inc(pos + 1) // we may have another number
	}
	t.composedNum = prevComposedNum // reset to a previous value
}

func TestSequentialDigits0(t *testing.T) {
	t.Logf("result=%v", sequentialDigits(100, 300))
}

/*
Best Time to Buy and Sell Stock
Say you have an array for which the ith element is the price of a given stock on day i.

If you were only permitted to complete at most one transaction (i.e., buy one and sell one share of the stock),
design an algorithm to find the maximum profit.

Note that you cannot sell a stock before you buy one.
*/

func maxProfitOneTransaction(prices []int) int {
	n := len(prices)
	if n == 0 {
		return 0
	}

	// find maximums after each element in the array
	maxAfter := make([]int, n)
	prevMax := 0
	for i := 0; i < n; i++ {
		maxAfter[n-i-1] = prevMax
		prevMax = intMax(prevMax, prices[n-i-1])
	}

	maxProfit := 0
	for i, price := range prices {
		maxProfit = intMax(maxProfit, maxAfter[i]-price)
	}
	return maxProfit
}

func maxProfitOneTransactionAlt(prices []int) int {
	// find maximums after each element in the array
	var minPrice, maxProfit int
	for i := 0; i < len(prices); i++ {
		if i == 0 || prices[i] < minPrice {
			minPrice = prices[i]
		} else if prices[i]-minPrice > maxProfit {
			maxProfit = prices[i] - minPrice
		}
	}
	return maxProfit
}

func TestMaxProfitOneTransactionBehaviorMatch(t *testing.T) {
	funcs := map[string]func([]int) int{
		"maxProfitOneTransaction":    maxProfitOneTransaction,
		"maxProfitOneTransactionAlt": maxProfitOneTransactionAlt,
	}

	testCases := map[int][]int{
		5: []int{7, 1, 5, 3, 6, 4},
		0: []int{7, 6, 4, 3, 1},
	}

	for funcName, f := range funcs {
		for expected, prices := range testCases {
			t.Run(fmt.Sprintf("%s: %v->%d", funcName, prices, expected), func(t *testing.T) {
				actual := f(prices)
				if actual != expected {
					t.Errorf("Got unexpected max profit: %d", actual)
				}
			})
		}
	}
}

/*
Robot Bounded In Circle
On an infinite plane, a robot initially stands at (0, 0) and faces north.  The robot can receive one of three instructions:

"G": go straight 1 unit;
"L": turn 90 degrees to the left;
"R": turn 90 degress to the right.
The robot performs the instructions given in order, and repeats them forever.

Return true if and only if there exists a circle in the plane such that the robot never leaves the circle.
*/

func isRobotBounded(instructions string) bool {
	var x, y, directionIndex int
	directions := [][]int{
		[]int{1, 0},
		[]int{0, 1},
		[]int{-1, 0},
		[]int{0, -1},
	}

	// compute coordinates for each step
	for i := 0; i < len(instructions); i++ {
		insn := instructions[i]
		switch insn {
		case 'R':
			directionIndex = (directionIndex + len(directions) - 1) % len(directions)
		case 'L':
			directionIndex = (directionIndex + 1) % len(directions)
		case 'G':
			d := directions[directionIndex]
			kx, ky := d[0], d[1]
			x, y = x+kx, y+ky
		default:
			panic("unknown command")
		}
	}
	if x == 0 && y == 0 {
		return true
	}

	// circle bounded can happen IFF robot returned to the same point or changes movement vector
	return directionIndex != 0 || (x == 0 && y == 0)
}

func TestRobotBounded(t *testing.T) {
	testCases := map[string]bool{
		"GLLG":   true,
		"GGLLGG": true,
		"GGLRG":  false,
		"GRLGG":  false,
		"GLGG":   true,
		"GL":     true,
		"GR":     true,
	}

	for dir, pass := range testCases {
		t.Run(fmt.Sprintf("%s -> %t", dir, pass), func(t *testing.T) {
			actual := isRobotBounded(dir)
			if pass != actual {
				t.Errorf("unexpected result: %t", actual)
			}
		})
	}
}

/*
Maximum XOR of Two Numbers in an Array
Given a non-empty array of numbers, a0, a1, a2, … , an-1, where 0 ≤ ai < 231.

Find the maximum result of ai XOR aj, where 0 ≤ i, j < n.

Could you do this in O(n) runtime?
*/

// TODO: O(n) runtime, O(n) memory solution - use prefix tree and two passes

// findMaximumXORBruteforce has O(n^2) runtime, O(1) memory
func findMaximumXORBruteforce(nums []int) int {
	max := 0
	for i, lhs := range nums {
		for j := i + 1; j < len(nums); j++ {
			rhs := nums[j]
			max = intMax(max, lhs^rhs)
		}
	}
	return max
}

func TestMaxXOR1(t *testing.T) {
	testCases := map[int][]int{
		28: []int{3, 10, 5, 25, 2, 8},
	}

	maxXORFuncs := map[string]func([]int) int{
		"findMaximumXORBruteforce": findMaximumXORBruteforce,
	}

	for funcName, maxXORFunc := range maxXORFuncs {
		for k, v := range testCases {
			t.Run(fmt.Sprintf("Test case for %s(%v)=%d", funcName, v, k), func(t *testing.T) {
				actual := maxXORFunc(v)
				if k != actual {
					t.Errorf("unexpected result: %d", actual)
				}
			})
		}
	}
}

/*
Length of Last Word
Given a string s consists of upper/lower-case alphabets and empty space characters ' ', return the length of last word
(last word means the last appearing word if we loop from left to right) in the string.

If the last word does not exist, return 0.

Note: A word is defined as a maximal substring consisting of non-space characters only.
*/

func lengthOfLastWord(s string) int {
	var lastLen int
	for i := 0; i < len(s); i++ {
		j := i
		for ; j < len(s); j++ {
			if s[j] == ' ' {
				break
			}
		}
		if j > i {
			lastLen = j - i
			i = j
		}
	}
	return lastLen
}

func TestLastLen(t *testing.T) {
	lengthOfLastWord("abc df")
}

/*
https://leetcode.com/explore/challenge/card/september-leetcoding-challenge/555/week-2-september-8th-september-14th/3459/
*/

func rob(nums []int) int {
	var m0, m1 int
	for i := 0; i < len(nums); i++ {
		m0, m1 = intMax(m0, m1), intMax(m1, m0+nums[i])
	}
	return m1
}

/*
Insert Interval
Given a set of non-overlapping intervals, insert a new interval into the intervals (merge if necessary).

You may assume that the intervals were initially sorted according to their start times.
*/

func insert(intervals [][]int, newInterval []int) [][]int {
	var result [][]int

	intersectIndex := 0
	for ; intersectIndex < len(intervals); intersectIndex++ {
		interval := intervals[intersectIndex]
		if interval[1] >= newInterval[0] {
			break
		}
		result = append(result, interval)
	}

	// no overlap, this should be the last interval
	if intersectIndex == len(intervals) {
		result = append(result, newInterval)
		return result
	}

	// compute overlap
	leftIntersectIndex, rightIntersectIndex := newInterval[0], newInterval[1]
	for ; intersectIndex < len(intervals); intersectIndex++ {
		intersectInterval := intervals[intersectIndex]
		if newInterval[1] < intersectInterval[0] {
			break
		}
		leftIntersectIndex = intMin(leftIntersectIndex, intersectInterval[0])
		rightIntersectIndex = intMax(rightIntersectIndex, intersectInterval[1])
	}
	result = append(result, []int{leftIntersectIndex, rightIntersectIndex})

	// add remaining
	for i := intersectIndex; i < len(intervals); i++ {
		result = append(result, intervals[i])
	}

	return result
}

func TestIntervals1(t *testing.T) {
	t.Run("singular interval", func(t *testing.T) {
		result := insert(
			[][]int{
				[]int{1, 5},
			},
			[]int{2, 3},
		)
		t.Logf("r = %v", result)
	})
}

func TestIntervals2(t *testing.T) {
	t.Run("ext first", func(t *testing.T) {
		result := insert(
			[][]int{
				[]int{1, 3}, []int{6, 9},
			},
			[]int{2, 5},
		)
		t.Logf("r = %v", result)
	})
}

/*
Combination Sum III
Find all possible combinations of k numbers that add up to a number n, given that only numbers from 1 to 9 can be used
and each combination should be a unique set of numbers.

Note:

All numbers will be positive integers.
The solution set must not contain duplicate combinations.
*/

func combinationSum3(k int, n int) [][]int {
	var t combinationSum3Finder
	t.n = n
	t.accum = make([]int, k)
	t.find(0, 1)
	return t.solutions
}

type combinationSum3Finder struct {
	n         int
	sum       int
	accum     []int
	solutions [][]int
}

func (t *combinationSum3Finder) find(pos int, num int) {
	if pos == len(t.accum) {
		if t.sum == t.n {
			var solution []int
			solution = append(solution, t.accum...)
			t.solutions = append(t.solutions, append(solution))
		}
		return
	}

	// [1..10) is the boundary we can try
	for i := num; i < 10; i++ {
		nextSum := t.sum + i
		if nextSum > t.n {
			return
		}
		t.sum = nextSum
		t.accum[pos] = i
		t.find(pos+1, i+1)
		t.sum -= i
	}
}

/*
Maximum Product Subarray
Given an integer array nums, find the contiguous subarray within an array (containing at least one number)
which has the largest product.
*/

func maxProduct(nums []int) int {
	if len(nums) == 0 {
		return 1
	}

	max := nums[0]
	prevMax := max
	prevMin := max
	for i := 1; i < len(nums); i++ {
		n := nums[i]
		curMax := intMax(n, intMax(n*prevMin, n*prevMax))
		curMin := intMin(n, intMin(n*prevMin, n*prevMax))
		max = intMax(max, curMax)
		prevMax = curMax
		prevMin = curMin
	}

	return max
}

func TestMaxProduct(t *testing.T) {
	testCases := map[int][]int{
		24:  []int{-2, 3, -4},
		108: []int{-1, -2, -9, -6},
	}

	for k, v := range testCases {
		t.Run(fmt.Sprintf("max product for %v", v), func(t *testing.T) {
			p := maxProduct(v)
			if p != k {
				t.Errorf("f(%v) produced %d which doesn't match expected %d product", v, p, k)
			}
		})
	}
}

/*
Bulls and Cows
You are playing the following Bulls and Cows game with your friend: You write down a number and ask your
friend to guess what the number is. Each time your friend makes a guess, you provide a hint that indicates how many
digits in said guess match your secret number exactly in both digit and position (called "bulls") and how many digits
match the secret number but locate in the wrong position (called "cows"). Your friend will use successive guesses
and hints to eventually derive the secret number.

Write a function to return a hint according to the secret number and friend's guess, use A to indicate the bulls
and B to indicate the cows.

Please note that both secret number and friend's guess may contain duplicate digits.
*/

func getHint(secret string, guess string) string {
	if len(secret) != len(guess) {
		return ""
	}

	// 1st pass: detect bulls and compute overall statistics for a secret
	bulls := 0
	cowStats := [10]int{}
	var guessDigits []byte
	for i := 0; i < len(secret); i++ {
		ch := secret[i]
		if ch == guess[i] {
			bulls++
			continue
		}

		secretDigit := secret[i] - '0'
		cowStats[secretDigit]++
		guessDigits = append(guessDigits, guess[i]-'0')
	}

	// 2nd pass: find out cows
	cows := 0
	for _, guessDigit := range guessDigits {
		cowStat := cowStats[guessDigit]
		if cowStat == 0 {
			continue
		}
		cows++
		cowStats[guessDigit] = cowStat - 1
	}

	return fmt.Sprintf("%dA%dB", bulls, cows)
}

/*
Compare Version Numbers

Compare two version numbers version1 and version2.
If version1 > version2 return 1; if version1 < version2 return -1;otherwise return 0.

You may assume that the version strings are non-empty and contain only digits and the . character.

The . character does not represent a decimal point and is used to separate number sequences.

For instance, 2.5 is not "two and a half" or "half way to version three", it is the fifth second-level revision of
the second first-level revision.

You may assume the default revision number for each level of a version number to be 0. For example, version number 3.4
has a revision number of 3 and 4 for its first and second level revision number.
Its third and fourth level revision number are both 0.

Note:

Version strings are composed of numeric strings separated by dots . and this numeric strings may have leading zeroes.
Version strings do not start or end with dots, and they will not be two consecutive dots.
*/

func compareVersion(version1 string, version2 string) int {
	var t1, t2 versionComponents
	t1.version = version1
	t2.version = version2
	for t1.hasNext() || t2.hasNext() {
		p1 := t1.next()
		p2 := t2.next()
		if p1 > p2 {
			return 1
		} else if p1 < p2 {
			return -1
		}
	}
	return 0
}

type versionComponents struct {
	version string
}

func (t *versionComponents) hasNext() bool {
	return len(t.version) > 0
}

func (t *versionComponents) next() int {
	if len(t.version) == 0 {
		return 0
	}

	pos := strings.IndexByte(t.version, '.')

	var nextVersion string
	if pos < 0 {
		pos = len(t.version)
		nextVersion = ""
	} else {
		nextVersion = t.version[pos+1:]
	}

	num, err := strconv.Atoi(t.version[0:pos])
	if err != nil {
		panic(err)
	}

	t.version = nextVersion

	return num
}

/*
Sum of Root To Leaf Binary Numbers
Given a binary tree, each node has value 0 or 1.
Each root-to-leaf path represents a binary number starting with the most significant bit.
For example, if the path is 0 -> 1 -> 1 -> 0 -> 1, then this could represent 01101 in binary, which is 13.

For all leaves in the tree, consider the numbers represented by the path from the root to that leaf.

Return the sum of these numbers.
*/

func sumRootToLeaf(root *TreeNode) int {
	var t sumRootState
	if root != nil {
		t.find(root, 0)
	}
	return t.sum
}

type sumRootState struct {
	sum int
}

func (t *sumRootState) find(n *TreeNode, num int) {
	nextNum := num<<1 + n.Val
	if n.Left == nil && n.Right == nil {
		t.sum += nextNum
		return
	}
	if n.Left != nil {
		t.find(n.Left, nextNum)
	}
	if n.Right != nil {
		t.find(n.Right, nextNum)
	}
}

/*
Word Pattern
Given a pattern and a string str, find if str follows the same pattern.

Here follow means a full match, such that there is a bijection between a letter in pattern and a non-empty word in str.
*/

func wordPattern(pattern string, str string) bool {
	wr := map[string]rune{} // word-to-rune
	rw := map[rune]string{} // rune-to-word

	j := 0
	for _, curRune := range pattern {
		// find next word in the given string
		wordStart := j
		for ; j < len(str); j++ {
			if str[j] != ' ' {
				continue // skip letters within the word
			}
			if wordStart != j {
				break // stop at trailing whitespace
			}
			wordStart++ // skip leading whitespace
		}
		if wordStart == j {
			return false // empty word means end of `str`
		}
		curWord := str[wordStart:j]

		// find if there is a corresponding word
		prevRune, runeExists := wr[curWord]
		prevWord, wordExists := rw[curRune]
		if runeExists != wordExists {
			return false
		}

		if runeExists { //==wordExists both word and rune mapping are in place and they both must match
			if prevRune != curRune || prevWord != curWord {
				return false
			}
			continue
		}

		// neither rune nor word exists
		wr[curWord] = curRune
		rw[curRune] = curWord
	}
	return j == len(str)
}

func TestWordPattern(t *testing.T) {
	testCases := map[string]bool{
		"abba;dog dog dog dog": false,
		"abba;dog cat cat dog": true,
	}

	for data, match := range testCases {
		matchStr := "mismatch"
		if match {
			matchStr = "match"
		}
		values := strings.Split(data, ";")

		t.Run(data, func(t *testing.T) {
			if match != wordPattern(values[0], values[1]) {
				t.Errorf("expect %s for pattern=%s and str=%s", matchStr, values[0], values[1])
			} else {
				t.Logf("properly produced %s for pattern=%s and str=%s", matchStr, values[0], values[1])
			}
		})
	}

	if wordPattern("abba", "dog dog dog dog") {
		t.Errorf("unexpected match")
	}
	t.Logf("done; r=%d", rand.Intn(10))
}

/*
Image Overlap
Two images A and B are given, represented as binary, square matrices of the same size.
(A binary matrix has only 0s and 1s as values.)

We translate one image however we choose (sliding it left, right, up, or down any number of units), and place
it on top of the other image.
After, the overlap of this translation is the number of positions that have a 1 in both images.
(Note also that a translation does not include any kind of rotation.)
What is the largest possible overlap?

Notes:

1 <= A.length = A[0].length = B.length = B[0].length <= 30
0 <= A[i][j], B[i][j] <= 1
*/

func largestOverlap(a [][]int, b [][]int) int {
	ma := normalizeMatrix(a)
	mb := normalizeMatrix(b)

	minHeight := intMin(len(a), len(b))
	minWidth := intMin(len(a[0]), len(b[0]))

	maxBits := 0

	for w := 1 - minWidth; w < minWidth; w++ {
		for h := 0; h < minHeight; h++ {
			maxBits = intMax(maxBits, findBitsCount(ma, mb, w, h))
			maxBits = intMax(maxBits, findBitsCount(mb, ma, w, h))
		}
	}

	return maxBits
}

func findBitsCount(ma, mb []uint32, w, h int) int {
	bitsCount := 0
	for rowA := 0; rowA < len(ma); rowA++ {
		rowB := h + rowA
		if rowB >= len(mb) {
			break
		}

		numA := ma[rowA]
		if w >= 0 {
			numA <<= w
		} else {
			numA >>= -w
		}
		numB := mb[rowB]

		bitsCount += bits.OnesCount32(numA & numB)
	}
	return bitsCount
}

func normalizeMatrix(m [][]int) []uint32 {
	result := make([]uint32, len(m))
	for h := 0; h < len(m); h++ {
		var row uint32
		r := m[h]
		for w := 0; w < len(r); w++ {
			row <<= 1
			if r[len(r)-w-1] != 0 {
				row |= 1
			}
		}
		result[h] = row
	}
	return result
}

func TestImageOverlap0(t *testing.T) {
	n := largestOverlap(
		[][]int{
			{0, 0, 0, 0, 0},
			{0, 1, 0, 0, 0},
			{0, 0, 1, 0, 0},
			{0, 0, 0, 0, 1},
			{0, 1, 0, 0, 1},
		},
		[][]int{
			{1, 0, 1, 1, 1},
			{1, 1, 1, 1, 1},
			{1, 1, 1, 1, 1},
			{0, 1, 1, 1, 1},
			{1, 0, 1, 1, 1},
		},
	)

	t.Logf("bits=%d", n)
	if n != 5 {
		t.Errorf("unexpected overlap: %d", n)
	}
}

func TestImageOverlap(t *testing.T) {

	t.Run("5d 5 bits overlap", func(t *testing.T) {
		n := largestOverlap(
			[][]int{
				{0, 0, 0, 0, 0},
				{0, 1, 0, 0, 0},
				{0, 0, 1, 0, 0},
				{0, 0, 0, 0, 1},
				{0, 1, 0, 0, 1},
			},
			[][]int{
				{1, 0, 1, 1, 1},
				{1, 1, 1, 1, 1},
				{1, 1, 1, 1, 1},
				{0, 1, 1, 1, 1},
				{1, 0, 1, 1, 1},
			},
		)

		t.Logf("bits=%d", n)
		if n != 5 {
			t.Errorf("unexpected overlap: %d", n)
		}
	})

	t.Run("3d 3 bits overlap", func(t *testing.T) {
		n := largestOverlap(
			[][]int{
				{1, 1, 0},
				{0, 1, 0},
				{0, 1, 0},
			},
			[][]int{
				{0, 0, 0},
				{0, 1, 1},
				{0, 0, 1},
			},
		)

		t.Logf("bits=%d", n)
		if n != 3 {
			t.Errorf("unexpected overlap: %d", n)
		}
	})

	t.Run("2d one bit overlap", func(t *testing.T) {
		n := largestOverlap(
			[][]int{
				{1, 0},
				{0, 1},
			},
			[][]int{
				{0, 1},
				{1, 0},
			},
		)

		t.Logf("bits=%d", n)
		if n != 1 {
			t.Errorf("unexpected overlap: %d", n)
		}
	})

	t.Run("3d - 3 bit overlap", func(t *testing.T) {
		n := largestOverlap(
			[][]int{
				{1, 1, 0},
				{0, 1, 0},
				{0, 1, 0},
			},
			[][]int{
				{0, 0, 0},
				{0, 1, 1},
				{0, 0, 1},
			},
		)

		t.Logf("bits=%d", n)
		if n != 3 {
			t.Errorf("unexpected overlap: %d", n)
		}
	})

	t.Run("3d - 3 bit overlap II", func(t *testing.T) {
		n := largestOverlap(
			[][]int{
				{1, 0, 1},
				{0, 1, 0},
				{1, 0, 1},
			},
			[][]int{
				{0, 1, 0},
				{1, 1, 1},
				{0, 1, 0},
			},
		)

		t.Logf("bits=%d", n)
		if n != 3 {
			t.Errorf("unexpected overlap: %d", n)
		}
	})

	t.Run("5d - 4 bits overlap", func(t *testing.T) {
		n := largestOverlap(
			[][]int{
				{0, 0, 0, 0, 0},
				{0, 1, 0, 0, 0},
				{0, 0, 1, 0, 0},
				{0, 0, 0, 0, 1},
				{0, 1, 0, 0, 1},
			},
			[][]int{
				{1, 0, 1, 1, 1},
				{1, 1, 1, 1, 1},
				{1, 1, 1, 1, 1},
				{0, 1, 1, 1, 1},
				{1, 0, 1, 1, 1},
			},
		)

		t.Logf("bits=%d", n)
		if n != 5 {
			t.Errorf("unexpected overlap: %d", n)
		}
	})

	t.Run("5d - 5 bit overlap", func(t *testing.T) {
		n := largestOverlap(
			[][]int{
				{0, 0, 0, 0, 0},
				{0, 0, 0, 1, 0},
				{0, 0, 1, 0, 0},
				{1, 0, 0, 0, 0},
				{1, 0, 0, 1, 0},
			},
			[][]int{
				{1, 1, 1, 0, 1},
				{1, 1, 1, 1, 1},
				{1, 1, 1, 1, 1},
				{1, 1, 1, 1, 0},
				{1, 1, 1, 0, 1},
			},
		)

		t.Logf("bits=%d", n)
		if n != 5 {
			t.Errorf("unexpected overlap: %d", n)
		}
	})
}

/*
All Elements in Two Binary Search Trees
Given two binary search trees root1 and root2.

Return a list containing all the integers from both trees sorted in ascending order.
*/

func getAllElements(root1 *TreeNode, root2 *TreeNode) []int {
	var result []int

	t1 := iterTreeNodeFrom(root1)
	t2 := iterTreeNodeFrom(root2)

	e1, ok1 := t1.next()
	e2, ok2 := t2.next()

	for ok1 && ok2 {
		for ok1 && ok2 && e1 <= e2 {
			result = append(result, e1)
			e1, ok1 = t1.next()
		}
		for ok1 && ok2 && e2 <= e1 {
			result = append(result, e2)
			e2, ok2 = t2.next()
		}
	}

	// feed in the remainder
	for ok1 {
		result = append(result, e1)
		e1, ok1 = t1.next()
	}
	for ok2 {
		result = append(result, e2)
		e2, ok2 = t2.next()
	}

	return result
}

type iterTreeNode struct {
	elems []*TreeNode
}

func iterTreeNodeFrom(r *TreeNode) *iterTreeNode {
	var t iterTreeNode
	t.feed(r)
	return &t
}

func (t *iterTreeNode) feed(r *TreeNode) {
	for r != nil {
		t.elems = append(t.elems, r)
		r = r.Left
	}
}

func (t *iterTreeNode) next() (int, bool) {
	size := len(t.elems)
	if size == 0 {
		return 0, false
	}
	last := t.elems[size-1]
	t.elems = t.elems[0 : size-1]
	t.feed(last.Right)
	return last.Val, true
}

/*
Partition Labels
A string S of lowercase English letters is given. We want to partition this string into as many parts as possible
so that each letter appears in at most one part, and return a list of integers representing the size of these parts.

Note:

S will have length in range [1, 500].
S will consist of lowercase English letters ('a' to 'z') only.
*/

func partitionLabels(s string) []int {
	var partitions []int

	charStats := map[byte]int{}
	for i := 0; i < len(s); i++ {
		ch := s[i]
		charStats[ch] = charStats[ch] + 1
	}

	partitionSize := 1
	accumulatedChars := map[byte]int{}
	for i := 0; i < len(s); i++ {
		ch := s[i]
		charCount := accumulatedChars[ch] + 1
		if charCount == charStats[ch] {
			delete(accumulatedChars, ch)
		} else {
			accumulatedChars[ch] = accumulatedChars[ch] + 1
		}

		if len(accumulatedChars) == 0 {
			partitions = append(partitions, partitionSize)
			partitionSize = 0
		}

		partitionSize++
	}

	return partitions
}

/* Fuzzy duplicate finder */

func containsNearbyAlmostDuplicate(nums []int, k int, t int) bool {
	if len(nums) == 0 {
		return false
	}

	for i := 1; i < len(nums); i++ {
		for j := 0; j < k; j++ {
			u := i - j - 1
			if u < 0 {
				break
			}
			if intAbs(nums[i]-nums[u]) <= t {
				return true
			}
		}
	}
	return false
}

/*
Delete Node in a BST
Given a root node reference of a BST and a key, delete the node with the given key in the BST. Return the root node reference (possibly updated) of the BST.

Basically, the deletion can be divided into two stages:

Search for a node to remove.
If the node is found, delete the node.
Note: Time complexity should be O(height of tree).
*/

func deleteNode(root *TreeNode, key int) *TreeNode {
	if root == nil {
		return nil
	}

	var sentinel TreeNode
	sentinel.Left = root

	prev := &sentinel.Left
	n := root

	for n != nil {
		if key == n.Val {
			break
		}

		if key > n.Val {
			// right tree
			prev = &n.Right
			n = n.Right
			continue
		}

		prev = &n.Left
		n = n.Left
	}

	if n == nil {
		return root // no key found, return tree as it is
	}

	// simplest cases - left or right subtree is null
	if n.Left == nil {
		*prev = n.Right
	} else if n.Right == nil {
		*prev = n.Left
	} else {
		// complex case: both subtrees are in place
		leftmost := treeMinusLeftmost(n.Right, &n.Right)
		n.Val = leftmost.Val
	}

	return sentinel.Left
}

func treeMinusLeftmost(r *TreeNode, prev **TreeNode) *TreeNode {
	for {
		if r.Left == nil {
			*prev = r.Right
			return r
		}
		prev = &r.Left
		r = r.Left
	}
}

func TestRemoval(t *testing.T) {
	k := deleteNode(
		&TreeNode{
			Val:   1,
			Right: &TreeNode{Val: 2},
		},
		2,
	)
	t.Logf("k.Val=%d", k.Val)
}

/*
Largest Component Size by Common Factor
Given a non-empty array of unique positive integers A, consider the following graph:

There are A.length nodes, labelled A[0] to A[A.length - 1];
There is an edge between A[i] and A[j] if and only if A[i] and A[j] share a common factor greater than 1.
Return the size of the largest connected component in the graph.
*/

func largestComponentSize(a []int) int {
	m := map[int]*lcsGroup{}
	groupIDCounter := 0
	for _, elem := range a {
		factors := lcsFactorize(elem)
		// reuse any existing group
		var group *lcsGroup
		for _, factor := range factors {
			foundGroup, exists := m[factor]
			if exists {
				group = foundGroup
				break
			}
		}
		// create new group if none was found
		if group == nil {
			groupIDCounter++
			group = &lcsGroup{groupID: groupIDCounter, primes: map[int]int{}, numbers: map[int]int{}}
		}
		group.numbers[elem] = 0
		// merge groups
		for _, factor := range factors {
			foundGroup, exists := m[factor]
			if exists {
				if foundGroup == group {
					continue // same group
				}

				// different groups, in this case we need to merge all primes from the found group into the current one
				for k := range foundGroup.primes {
					group.primes[k] = 0
				}
				for k := range foundGroup.numbers {
					group.numbers[k] = 0
				}
			}

			group.primes[factor] = 0
		}
		// finally update all collected primes to point to the found group
		for k := range group.primes {
			m[k] = group
		}

		lcsDBGDump(elem, factors, m)
	}

	// finally find connection factor
	max := 0
	for _, group := range m {
		connFactor := len(group.numbers)
		if max < connFactor {
			max = connFactor
		}
	}

	lcsDBGFinalValidation(m, a)
	return max
}

const lcsMaxNumber = 100000

var lcsPrimes = []int{
	2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
	113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239,
	241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
}

func lcsFactorize(num int) []int {
	var factors []int

	for _, prime := range lcsPrimes {
		if num%prime == 0 {
			factors = append(factors, prime)
			continue
		}

		if prime > num {
			break
		}
	}

	if len(factors) == 0 {
		// this number is a prime itself
		factors = append(factors, num)
	}

	return factors
}

type lcsGroup struct {
	groupID int
	primes  map[int]int
	numbers map[int]int
}

func lcsDBGDump(elem int, factors []int, m map[int]*lcsGroup) {
	// debug dump state
	fmt.Printf("[LCS] factorizing %d -> %v\n", elem, factors)
	printedGroups := map[int]bool{}
	for k, v := range m {
		fmt.Printf("\t%7d -> {groupId: %d, numbers: [", k, v.groupID)
		if printedGroups[v.groupID] {
			fmt.Printf("... same as above ...]}\n")
			continue
		}
		printedGroups[v.groupID] = true
		for k := range v.numbers {
			fmt.Printf(" %d", k)
		}
		fmt.Printf(" ], primes: [")
		for k := range v.primes {
			fmt.Printf(" %d", k)
		}
		fmt.Printf(" ]}\n")
	}
}

func lcsDBGFinalValidation(m map[int]*lcsGroup, a []int) {
	numToGroupID := map[int]int{}
	for _, group := range m {
		for k := range group.numbers {
			prevGroupID, exists := numToGroupID[k]
			if exists {
				if prevGroupID != group.groupID {
					panic(fmt.Sprintf("Group mismatch: got %d and %d", prevGroupID, group.groupID))
				}
				continue
			}
			numToGroupID[k] = group.groupID
		}
	}
	for _, num := range a {
		_, exists := numToGroupID[num]
		if !exists {
			panic(fmt.Sprintf("Num %d is missing in the map", num))
		}
	}
	fmt.Printf("Num-to-groupID looks good\n")
}

func TestLargestComponentSize1(t *testing.T) {
	//n := largestComponentSize([]int{2, 2 * 3, 7, 7 * 5, 2 * 5, 11, 17})
	//n := largestComponentSize([]int{2, 3, 6, 7, 4, 12, 21, 39})
	n := largestComponentSize([]int{2, 7, 522, 526, 535, 26, 944, 35, 519, 45, 48, 567, 266, 68, 74, 591, 81, 86, 602, 93, 610, 621, 111, 114, 629, 641, 131, 651, 142, 659, 669, 161, 674, 163, 180, 187, 190, 194, 195, 206, 207, 218, 737, 229, 240, 757, 770, 260, 778, 270, 272, 785, 274, 290, 291, 292, 296, 810, 816, 314, 829, 833, 841, 349, 880, 369, 147, 897, 387, 390, 905, 405, 406, 407, 414, 416, 417, 425, 938, 429, 432, 926, 959, 960, 449, 963, 966, 929, 457, 463, 981, 985, 79, 487, 1000, 494, 508})
	t.Logf("[1] n=%d", n)
}

/*
Pancake Sorting
Given an array of integers A, We need to sort the array performing a series of pancake flips.

In one pancake flip we do the following steps:

Choose an integer k where 0 <= k < A.length.
Reverse the sub-array A[0...k].
For example, if A = [3,2,1,4] and we performed a pancake flip choosing k = 2, we reverse the sub-array [3,2,1],
so A = [1,2,3,4] after the pancake flip at k = 2.

Return an array of the k-values of the pancake flips that should be performed in order to sort A. Any valid answer
that sorts the array within 10 * A.length flips will be judged as correct.

1 <= A.length <= 100
1 <= A[i] <= A.length
All integers in A are unique (i.e. A is a permutation of the integers from 1 to A.length).
*/

func pancakeSort(a []int) []int {
	var result []int

	b := make([]int, len(a))
	copy(b, a)

	for last := len(b) - 1; last > 0; last-- {
		maxPos := 0
		max := b[0]
		for i := 1; i <= last; i++ {
			if max < b[i] {
				max = b[i]
				maxPos = i
			}
		}

		if maxPos == last {
			continue // biggest element is at its desired pos
		}

		if maxPos != 0 {
			// move max element to the very beginning
			result = append(result, maxPos+1)
			pancakeMove(b, maxPos+1)
		}

		result = append(result, last+1)
		pancakeMove(b, last+1)
	}
	return result
}

func pancakeMove(a []int, k int) {
	for i := 0; i < k/2; i++ {
		a[i], a[k-i-1] = a[k-i-1], a[i]
	}
}

func applyPancakeSort(a []int, k []int) []int {
	result := make([]int, len(a))
	copy(result, a)
	for _, r := range k {
		pancakeMove(result, r)
	}
	return result
}

func TestPancakeSort(t *testing.T) {
	a := []int{3, 2, 4, 1}
	k := pancakeSort(a)
	//k := []int{4, 2, 4, 3}
	n := applyPancakeSort(a, k)
	t.Logf("a=%v, k=%v; n=%v", a, k, n)
}

/*
Implement Rand10() Using Rand7()
Given a function rand7 which generates a uniform random integer in the range 1 to 7,
write a function rand10 which generates a uniform random integer in the range 1 to 10.

Do NOT use system's Math.random().
*/

func rand10() int {
	rand40 := 41
	for rand40 > 40 {
		rand40 = rand7() + 7*(rand7()-1)
	}
	return rand40 - 10*((rand40-1)/10)
}

func rand7() int {
	return rand.Intn(7) + 1
}

/*
Sum of Left Leaves
Find the sum of all left leaves in a given binary tree.
*/

func sumOfLeftLeaves(root *TreeNode) int {
	var findSum func(n *TreeNode, multiplier int) int
	findSum = func(n *TreeNode, multiplier int) int {
		if n == nil {
			return 0
		}
		if n.Left == nil && n.Right == nil {
			return multiplier * n.Val
		}
		return findSum(n.Left, 1) + findSum(n.Right, 0)
	}
	return findSum(root, 0)
}

/*
Stream of Characters
Implement the StreamChecker class as follows:

StreamChecker(words): Constructor, init the data structure with the given words.
query(letter): returns true if and only if for some k >= 1, the last k characters queried (in order from
	oldest to newest, including this letter just queried) spell one of the words in the given list.

	Note:
1 <= words.length <= 2000
1 <= words[i].length <= 2000
Words will only consist of lowercase English letters.
Queries will only consist of lowercase English letters.
The number of queries is at most 40000.
*/

type socNode struct {
	children [26]*socNode
	leaf     bool
	//debugStr string
}

type socStreamChecker struct {
	root       socNode
	queryNodes []*socNode
}

func socConstructor(words []string) socStreamChecker {
	var s socStreamChecker
	for _, w := range words {
		it := &s.root
		for n := 0; n < len(w); n++ {
			index := w[n] - 'a'
			next := it.children[index]
			if next == nil {
				next = &socNode{}
				it.children[index] = next
				//next.debugStr = w[0 : n+1]
			}
			it = next
		}
		it.leaf = true
	}
	return s
}

func (t *socStreamChecker) Query(letter byte) bool {
	result := false
	index := letter - 'a'

	t.queryNodes = append(t.queryNodes, &t.root)
	last := len(t.queryNodes) - 1
	for i := 0; i <= last; i++ {
		it := t.queryNodes[i]

		next := it.children[index]
		if next != nil {
			t.queryNodes[i] = next
			result = result || next.leaf
			continue
		}
		// this is not a part of any word
		t.queryNodes[i], t.queryNodes[last] = t.queryNodes[last], t.queryNodes[i]
		if i != last {
			i--
		}
		// resize array to exclude last element
		t.queryNodes = t.queryNodes[0:last]
		last--
	}

	return result
}

func TestStreamOfCharacters1(t *testing.T) {
	c := socConstructor([]string{"cd", "f", "kl"})
	chars := "abcdefghijklm"
	for _, ch := range []byte(chars) {
		result := c.Query(ch)
		t.Logf("Query(%c)=%t", ch, result)
	}
}

func TestStreamOfCharacters2(t *testing.T) {
	c := socConstructor([]string{"aa", "baa", "baaa", "aaa", "bbbb"})
	chars := "bababab"
	for _, ch := range []byte(chars) {
		result := c.Query(ch)
		t.Logf("Query(%c)=%t", ch, result)
	}
}

/*
Random Point in Non-overlapping Rectangles
Given a list of non-overlapping axis-aligned rectangles rects, write a function pick which randomly and uniformily picks an integer point in the space covered by the rectangles.

Note:

An integer point is a point that has integer coordinates.
A point on the perimeter of a rectangle is included in the space covered by the rectangles.
ith rectangle = rects[i] = [x1,y1,x2,y2], where [x1, y1] are the integer coordinates of the bottom-left corner, and [x2, y2] are the integer coordinates of the top-right corner.
length and width of each rectangle does not exceed 2000.
1 <= rects.length <= 100
pick return a point as an array of integer coordinates [p_x, p_y]
pick is called at most 10000 times.
*/

type rpnSolution struct {
	rects       []*rpnRect
	totalWeight int
}

func (t *rpnSolution) Len() int           { return len(t.rects) }
func (t *rpnSolution) Less(i, j int) bool { return t.rects[i].weight < t.rects[j].weight }
func (t *rpnSolution) Swap(i, j int)      { t.rects[i], t.rects[j] = t.rects[j], t.rects[i] }

type rpnRect struct {
	left   int
	bottom int
	width  int
	height int
	weight int
}

func rpnConstructor(rects [][]int) rpnSolution {
	var s rpnSolution

	weight := 0
	for _, rect := range rects {
		n := &rpnRect{
			left:   rect[0],
			bottom: rect[1],
			width:  rect[2] - rect[0] + 1,
			height: rect[3] - rect[1] + 1,
			weight: weight,
		}
		s.rects = append(s.rects, n)
		weight += n.width * n.height
	}

	sort.Sort(&s)
	s.totalWeight = weight

	return s
}

// Pick picks random dot within any of the given rects
func (t *rpnSolution) Pick() []int {
	dot := int(rand.Int31n(int32(t.totalWeight)))
	rectIndex := sort.Search(len(t.rects), func(pos int) bool {
		return dot < t.rects[pos].weight
	})
	r := t.rects[rectIndex-1]
	rectDot := dot - r.weight
	left := rectDot % r.width
	bottom := rectDot / r.width
	return []int{r.left + left, r.bottom + bottom}
}

func TestRandomPick1(t *testing.T) {
	s := rpnConstructor([][]int{{1, 1, 2, 2}})
	for i := 0; i < 20; i++ {
		t.Logf("randomPick(%d) -> %v", i, s.Pick())
	}
}

func TestRandomPick2(t *testing.T) {
	s := rpnConstructor([][]int{{1, 1, 5, 51}})
	for i := 0; i < 20; i++ {
		t.Logf("randomPick(%d) -> %v", i, s.Pick())
	}
	//[[82918473, -57180867, 82918476, -57180863], [83793579, 18088559, 83793580, 18088560], [66574245, 26243152, 66574246, 26243153], [72983930, 11921716, 72983934, 11921720]]
}

/*
Reorder List
Given a singly linked list L: L0→L1→…→Ln-1→Ln,
reorder it to: L0→Ln→L1→Ln-1→L2→Ln-2→…

You may not modify the values in the list's nodes, only nodes itself may be changed.
*/

func reorderList(head *ListNode) {
	if head == nil {
		return
	}

	count := 0
	for it := head; it != nil; it = it.Next {
		count++
	}

	medianPos := count / 2
	// find median element
	median := head
	for i := 0; i < medianPos; i++ {
		median = median.Next
	}

	// reorder elements after median
	it := median.Next
	median.Next = nil // this is going to be the tail
	var last *ListNode
	for it != nil {
		tmp := it.Next
		it.Next = last
		last, it = it, tmp
	}

	// now reorder elements starting at head
	for it = head; last != nil; {
		tmp := last.Next
		last.Next = it.Next
		it.Next = last
		it, last = last.Next, tmp
	}
}

type ListNode struct {
	Val  int
	Next *ListNode
}

func newList(nums ...int) *ListNode {
	var source ListNode
	it := &source.Next
	for _, n := range nums {
		node := &ListNode{Val: n}
		*it = node
		it = &node.Next
	}
	return source.Next
}

func (t *ListNode) String() string {
	var sb strings.Builder
	sb.WriteByte('[')
	for it := t; it != nil; it = it.Next {
		if it != t {
			sb.WriteString(", ")
		}
		sb.WriteString(strconv.Itoa(it.Val))
	}
	sb.WriteByte(']')
	return sb.String()
}

func TestListNode(t *testing.T) {
	l1 := newList(1, 2, 3, 4)
	l1Str := l1.String()
	reorderList(l1)
	t.Logf("l1=%s, reorder=%s", l1Str, l1)

	l2 := newList(1, 2, 3)
	l2Str := l2.String()
	reorderList(l2)
	t.Logf("l2=%s, reorder=%s", l2Str, l2)
}

/*
Goat Latin
A sentence S is given, composed of words separated by spaces. Each word consists of lowercase and uppercase letters only.

We would like to convert the sentence to "Goat Latin" (a made-up language similar to Pig Latin.)

The rules of Goat Latin are as follows:

If a word begins with a vowel (a, e, i, o, or u), append "ma" to the end of the word.
For example, the word 'apple' becomes 'applema'.

If a word begins with a consonant (i.e. not a vowel), remove the first letter and append it to the end, then add "ma".
For example, the word "goat" becomes "oatgma".

Add one letter 'a' to the end of each word per its word index in the sentence, starting with 1.
For example, the first word gets "a" added to the end, the second word gets "aa" added to the end and so on.
Return the final sentence representing the conversion from S to Goat Latin.
*/

func toGoatLatin(s string) string {
	var p goatLatinStreamProcessor
	for i := 0; i < len(s); i++ {
		p.feed(s[i])
	}
	p.feed(0)
	return p.w.String()
}

type goatLatinStreamProcessor struct {
	w     strings.Builder
	state goatLatinParserState

	wordCount int
	consonant byte
}

func (t *goatLatinStreamProcessor) appendSuffix() {
	if t.consonant != 0 {
		t.w.WriteByte(t.consonant)
	}
	t.w.WriteString("ma")
	for i := 0; i <= t.wordCount; i++ {
		t.w.WriteByte('a')
	}
}

func (t *goatLatinStreamProcessor) feed(ch byte) {
	// whitespace or end of word?
	if ch == ' ' || ch == 0 {
		if t.state == goatLatWord {
			t.appendSuffix()
			// update state
			t.consonant = 0
			t.wordCount++
			t.state = goatLatWS
		}
		if ch > 0 {
			t.w.WriteByte(ch)
		}
		return
	}

	// first character?
	if t.state == goatLatWS {
		lowercaseCh := ch | ('a' - 'A')
		switch lowercaseCh {
		case 'a', 'e', 'i', 'o', 'u':
			t.w.WriteByte(ch)
			break
		default:
			t.consonant = ch
		}
		t.state = goatLatWord
		return
	}

	// this should be a mid-word
	t.w.WriteByte(ch)
}

type goatLatinParserState int

const (
	goatLatWS = iota
	goatLatWord
)

/*
Numbers With Same Consecutive Differences
Return all non-negative integers of length N such that the absolute difference between every two consecutive digits is K.

Note that every number in the answer must not have leading zeros except for the number 0 itself. For example, 01 has one leading zero and is invalid, but 0 is valid.

You may return the answer in any order.
*/

func numsSameConsecDiff(n int, k int) []int {
	var d consecDiffFinder
	d.k = k
	d.max = 1
	for i := 0; i < n; i++ {
		d.max *= 10
	}
	if n == 1 {
		d.result = []int{0}
	}
	for i := 1; i <= 9; i++ {
		d.scan(i)
	}
	return d.result
}

type consecDiffFinder struct {
	result []int
	max    int
	k      int
}

func (t *consecDiffFinder) scan(n int) {
	newN := n * 10

	if newN >= t.max {
		t.result = append(t.result, n)
		return
	}

	digit := n % 10

	predDigit := digit - t.k
	if predDigit >= 0 {
		t.scan(newN + predDigit)
	}
	nextDigit := digit + t.k
	if nextDigit <= 9 && nextDigit != predDigit {
		t.scan(newN + nextDigit)
	}
}

/*
Best Time to Buy and Sell Stock III
Say you have an array for which the ith element is the price of a given stock on day i.

Design an algorithm to find the maximum profit. You may complete at most two transactions.

Note: You may not engage in multiple transactions at the same time (i.e., you must sell the stock before you buy again).
*/

func maxProfit(prices []int) int {
	if len(prices) == 0 {
		return 0
	}

	n := len(prices)

	maxAfter := make([]int, n)
	maxBefore := make([]int, n)

	for i := 0; i < n; i++ {
		for j := i + 1; j < n; j++ {
			curProfitBefore := prices[j] - prices[i]
			maxBefore[j] = intMax(maxBefore[j], intMax(maxBefore[j-1], curProfitBefore))

			curProfitAfter := prices[n-i-1] - prices[n-j-1]
			maxAfter[n-j-1] = intMax(maxAfter[n-j-1], intMax(maxAfter[n-j], curProfitAfter))
		}
	}

	//fmt.Printf("maxBefore: %v\nmaxAfter:  %v\n", maxBefore, maxAfter)

	maxProfit := 0
	for i := 1; i < n; i++ {
		localMax := maxBefore[i]
		if i+1 < n {
			localMax += maxAfter[i+1]
		}
		maxProfit = intMax(maxProfit, localMax)
	}

	return maxProfit
}

func TestProfit1(t *testing.T) {
	t.Logf("t(0)=%d", maxProfit([]int{3, 3, 5, 0, 0, 3, 1, 4}))
}

/*
Non-overlapping Intervals
Given a collection of intervals, find the minimum number of intervals you need to remove to
make the rest of the intervals non-overlapping.
*/

type intervals [][]int

func (p intervals) Len() int           { return len(p) }
func (p intervals) Less(i, j int) bool { return p[i][0] < p[j][0] }
func (p intervals) Swap(i, j int)      { p[i], p[j] = p[j], p[i] }

func eraseOverlapIntervals(rawIntervals [][]int) int {
	if len(rawIntervals) == 0 {
		return 0
	}

	intv := intervals(rawIntervals)
	sort.Sort(intv)

	minEnd := intv[0][1]
	result := 0
	for i := 1; i < len(intv); i++ {
		iv := intv[i]
		if iv[0] < minEnd {
			if minEnd >= iv[1] {
				minEnd = iv[1]
			}

			result++
		} else {
			minEnd = iv[1]
		}
	}

	return result
}

func TestNonOverlappingIntervals(t *testing.T) {
	t.Logf("r(1)=%d", eraseOverlapIntervals([][]int{{1, 100}, {11, 22}, {1, 11}, {2, 12}}))
}

/*
Longest Palindrome
Given a string which consists of lowercase or uppercase letters, find the length of the longest palindromes that can be built with those letters.

This is case sensitive, for example "Aa" is not considered a palindrome here.

Note:
Assume the length of given string will not exceed 1,010.
*/

func longestPalindrome(s string) int {
	m := map[byte]int{}
	for i := 0; i < len(s); i++ {
		ch := s[i]
		m[ch] = m[ch] + 1
	}

	result := 0
	singleCharCounted := false
	for _, v := range m {
		if v%2 == 1 {
			result += v - 1
			if !singleCharCounted {
				result++
				singleCharCounted = true
			}
		} else {
			result += v
		}
	}
	return result
}

/*
Iterator for Combination
Design an Iterator class, which has:

A constructor that takes a string characters of sorted distinct lowercase
English letters and a number combinationLength as arguments.
A function next() that returns the next combination of length combinationLength in lexicographical order.
A function hasNext() that returns True if and only if there exists a next combination.
*/

type mtCombinationIterator struct {
	chars   string
	markers []int
}

func mtConstructor(characters string, combinationLength int) mtCombinationIterator {
	t := mtCombinationIterator{chars: characters, markers: make([]int, combinationLength)}
	for i := 0; i < combinationLength; i++ {
		t.markers[i] = i
	}

	return t
}

func (t *mtCombinationIterator) rollNext(markerIndex int) bool {
	if markerIndex >= len(t.markers) {
		return false
	}

	if t.rollNext(markerIndex + 1) {
		return true
	}

	nextPos := t.markers[markerIndex] + 1
	if nextPos >= len(t.chars) {
		t.markers[markerIndex] = len(t.chars)
		return false
	}

	t.markers[markerIndex] = nextPos
	for i := markerIndex + 1; i < len(t.markers); i++ {
		nextPos++
		if nextPos >= len(t.chars) {
			t.markers[markerIndex] = len(t.chars)
			return false
		}
		t.markers[i] = nextPos
	}

	return true
}

func (t *mtCombinationIterator) Next() string {
	// record combination
	result := make([]byte, len(t.markers))
	for i := 0; i < len(t.markers); i++ {
		result[i] = t.chars[t.markers[i]]
	}

	// roll to the next position
	t.rollNext(0)

	return string(result)
}

func (t *mtCombinationIterator) HasNext() bool {
	return len(t.markers) > 0 && t.markers[0] < len(t.chars)
}

func collectCombinations(s string, l int) []string {
	var result []string
	c := mtConstructor(s, l)
	for c.HasNext() {
		result = append(result, c.Next())
	}
	return result
}

func TestCombinationLength(t *testing.T) {
	t.Logf("f(abc, 1)=%v", collectCombinations("abc", 1))
	t.Logf("f(abcd, 2)=[%s]", strings.Join(collectCombinations("abcd", 2), ", "))
	t.Logf("f(ab, 2)=%v", collectCombinations("ab", 2))
	t.Logf("f(abc, 2)=[%s]", strings.Join(collectCombinations("abc", 2), ", "))
	t.Logf("f(abcd, 3)=[%s]", strings.Join(collectCombinations("abcd", 3), ", "))
}

/*
Pascal's Triangle II
Given a non-negative index k where k ≤ 33, return the kth index row of the Pascal's triangle.

Note that the row index starts from 0.
*/

func getRow(rowIndex int) []int {
	len := rowIndex + 1
	result := make([]int, len)
	result[0] = 1
	for i := 1; i <= rowIndex; i++ {
		half := (i + 1) / 2
		prev := result[0] // always == 1
		for j := 1; j < half; j++ {
			tmp := result[j]
			result[j] += prev
			prev = tmp
		}
		if i%1 == 0 {
			result[half] = prev + prev
		}
	}

	for i := 0; i < len/2; i++ {
		result[len-i-1] = result[i]
	}

	return result
}

func TestGetRow(t *testing.T) {
	t.Logf("r=%v", getRow(4))
}

/*
H-Index
Given an array of citations (each citation is a non-negative integer) of a researcher, write
a function to compute the researcher's h-index.

According to the definition of h-index on Wikipedia: "A scientist has index h if h of his/her N papers have
at least h citations each, and the other N − h papers have no more than h citations each."
*/

func hIndex(citations []int) int {
	// solution: sort+binary search
	sort.Ints(citations)
	result := 0

	left := 0
	right := len(citations)
	for left < right {
		median := (left + right) / 2
		h := len(citations) - median
		if h <= citations[median] {
			result = h
			right = median
			continue
		}

		left = median + 1
	}

	return result
}

/*
Rotting Oranges
In a given grid, each cell can have one of three values:

the value 0 representing an empty cell;
the value 1 representing a fresh orange;
the value 2 representing a rotten orange.
Every minute, any fresh orange that is adjacent (4-directionally) to a rotten orange becomes rotten.

Return the minimum number of minutes that must elapse until no cell has a fresh orange.  If this is impossible, return -1 instead.
*/

func orangesRotting(grid [][]int) int {
	if len(grid) == 0 || len(grid[0]) == 0 {
		return 0
	}

	height := len(grid)
	width := len(grid[0])

	fresh := map[int]coord{}
	for h := 0; h < height; h++ {
		for w := 0; w < width; w++ {
			if grid[h][w] == 1 {
				fresh[len(fresh)] = coord{h, w}
			}
		}
	}

	days := 0

	for ; len(fresh) > 0; days++ {
		var rot []int
		for pos, c := range fresh {
			if c.w > 0 && grid[c.h][c.w-1] == 2 {
				rot = append(rot, pos)
			} else if c.w < (width-1) && grid[c.h][c.w+1] == 2 {
				rot = append(rot, pos)
			} else if c.h > 0 && grid[c.h-1][c.w] == 2 {
				rot = append(rot, pos)
			} else if c.h < (height-1) && grid[c.h+1][c.w] == 2 {
				rot = append(rot, pos)
			}
		}

		if len(rot) == 0 {
			return -1
		}
		for _, pos := range rot {
			c := fresh[pos]
			grid[c.h][c.w] = 2
			delete(fresh, pos)
		}
	}

	return days
}

type coord struct{ h, w int }

//
// Samples
//

func isPalindrome(s string) bool {
	re := regexp.MustCompile(`[[:^alnum:]]`)
	s = string(re.ReplaceAll([]byte(strings.ToLower(s)), []byte("")))
	for i := 0; i < len(s)/2; i++ {
		j := len(s) - i - 1
		if s[i] != s[j] {
			return false
		}
	}
	return true
}

//
// Power of Four
//

const epsilon = 0.00000001

func isPowerOfFour(num int) bool {
	if num <= 0 {
		return false
	}
	if num == 1 {
		return true
	}

	n := math.Log(float64(num)) / math.Log(float64(4))
	if math.Abs(math.Round(n)-n) < epsilon {
		return true
	}
	return false
}

//
// Add and Search Word - Data structure design
//

type wordNode struct {
	children     map[byte]*wordNode
	completeWord bool
}

func newWordNode() *wordNode {
	return &wordNode{children: map[byte]*wordNode{}}
}

type WordDictionary struct {
	root *wordNode
}

/** Initialize your data structure here. */
func Constructor2() WordDictionary {
	return WordDictionary{
		root: newWordNode(),
	}
}

/** Adds a word into the data structure. */
func (this *WordDictionary) AddWord(word string) {
	n := this.root
	for i := 0; i < len(word); i++ {
		ch := word[i]
		next := n.children[ch]
		if next == nil {
			next = newWordNode()
			n.children[ch] = next
		}
		n = next
	}
	n.completeWord = true
}

func recursiveMatch(word string, pos int, node *wordNode) bool {
	if node == nil {
		return false
	}

	if pos >= len(word) {
		return node.completeWord
	}

	for ; node != nil && pos < len(word); pos++ {
		ch := word[pos]
		if ch != '.' {
			node = node.children[ch]
			continue
		}

		// dot-symbol, try all available children
		for _, childNode := range node.children {
			if recursiveMatch(word, pos+1, childNode) {
				return true // a match has been found
			}
		}
		return false // none matched
	}

	if node == nil {
		return false
	}

	return node.completeWord
}

/** Returns if the word is in the data structure. A word could contain the dot character '.' to represent any one letter. */
func (this *WordDictionary) Search(word string) bool {
	return recursiveMatch(word, 0, this.root)
}

//
// Find All Duplicates in an Array
//

func findDuplicates(nums []int) []int {
	var result []int

	for i := 0; i < len(nums); i++ {
		// we're moving an element from the source position to the target position
		sourcePos := i
		targetPos := nums[sourcePos] - 1
		if sourcePos == targetPos {
			continue // an element is where it belongs to
		}
		nums[sourcePos] = -1 // we'll be moving element from the source pos to the target pos

		for targetPos >= 0 {
			nextPos := nums[targetPos] - 1  // an element at the target position
			nums[targetPos] = targetPos + 1 // set element where it belongs to

			if nextPos == targetPos {
				// found a duplicate where we currently are
				result = append(result, targetPos+1)
				break
			}

			// found occupied slot which needs to be moved further
			targetPos = nextPos
			sourcePos = targetPos
		}
	}

	return result
}

func TestFindDuplicate(t *testing.T) {
	findDuplicates([]int{4, 1, 3, 2, 2, 1})
}

/*
Path Sum III
You are given a binary tree in which each node contains an integer value.

Find the number of paths that sum to a given value.

The path does not need to start or end at the root or a leaf, but it must go downwards (traveling only from parent nodes to child nodes).

The tree has no more than 1,000 nodes and the values are in the range -1,000,000 to 1,000,000.
*/

func pathSum(root *TreeNode, sum int) int {
	pf := pathSumFinder{targetSum: sum, intermediateSums: map[int]int{}}
	pf.scan(root, 0)
	return pf.result
}

type pathSumFinder struct {
	targetSum        int
	intermediateSums map[int]int
	result           int
}

func (t *pathSumFinder) scan(n *TreeNode, curSum int) {
	if n == nil {
		return
	}

	nextSum := curSum + n.Val
	diff := nextSum - t.targetSum
	cnt := t.intermediateSums[diff]

	t.result += cnt
	if nextSum == t.targetSum {
		t.result++
	}

	nextSumPrevCount := t.intermediateSums[nextSum]
	t.intermediateSums[nextSum] = nextSumPrevCount + 1

	t.scan(n.Left, nextSum)
	t.scan(n.Right, nextSum)

	t.intermediateSums[nextSum] = nextSumPrevCount
}

func TestPathSum0(t *testing.T) {
	k := pathSum(&TreeNode{Val: 1}, 0)
	if k != 0 {
		t.Errorf("k=%d", k)
	}
}

func TestPathSum1(t *testing.T) {
	k := pathSum(&TreeNode{
		Val: 5,
		Left: &TreeNode{
			Val: 4,
			Left: &TreeNode{
				Val:   11,
				Left:  &TreeNode{Val: 7},
				Right: &TreeNode{Val: 2},
			},
		},
		Right: &TreeNode{
			Val:  8,
			Left: &TreeNode{Val: 13},
			Right: &TreeNode{
				Val:   4,
				Left:  &TreeNode{Val: 5},
				Right: &TreeNode{Val: 1},
			},
		},
	}, 22)
	if k != 3 {
		t.Errorf("k=%d", k)
	}
}

/*
Minimum Cost For Tickets
In a country popular for train travel, you have planned some train travelling one year in advance.
The days of the year that you will travel is given as an array days.  Each day is an integer from 1 to 365.

Train tickets are sold in 3 different ways:

a 1-day pass is sold for costs[0] dollars;
a 7-day pass is sold for costs[1] dollars;
a 30-day pass is sold for costs[2] dollars.
The passes allow that many days of consecutive travel.  For example, if we get a 7-day pass on day 2,
then we can travel for 7 days: day 2, 3, 4, 5, 6, 7, and 8.

Return the minimum number of dollars you need to travel every day in the given list of days.
*/

func mincostTickets(days []int, costs []int) int {
	totalDays := len(days)
	dp := make([]int, totalDays+1) // bottom-up approach: fill from last element to the first one
	cc := make([]int, len(costs))  // cost choices: indices of dp between now (index i) and i+corresponding number of days
	passLengths := []int{1, 7, 30} // number of days per each pass, indices in this array must match costs length
	if len(passLengths) != len(costs) {
		panic("invalid choice of costs") // it could also be passed as a parameter
	}
	for i := totalDays - 1; i >= 0; i-- {
		// fill out cost choices
		for j := 0; j < len(cc); j++ {
			cc[j] = i
			for cc[j] < totalDays && days[cc[j]] < days[i]+passLengths[j] {
				cc[j]++
			}
		}

		// find min cost
		dp[i] = math.MaxInt32
		for j := 0; j < len(cc); j++ {
			dp[i] = intMin(dp[i], costs[j]+dp[cc[j]])
		}
	}
	return dp[0]
}

/*
Largest Time for Given Digits
Given an array of 4 digits, return the largest 24 hour time that can be made.

The smallest 24 hour time is 00:00, and the largest is 23:59.  Starting from 00:00,
a time is larger if more time has elapsed since midnight.

Return the answer as a string of length 5.  If no valid time can be made, return an empty string.
*/

func largestTimeFromDigits(a []int) string {
	r := make([]int, 4)
	max := -1

	for d0 := 0; d0 < 4; d0++ {
		a0 := a[d0]
		if a0 > 2 {
			continue
		}
		for d1 := 0; d1 < 4; d1++ {
			a1 := a[d1]
			if d1 == d0 || (a0 == 2 && a1 > 3) {
				continue
			}
			for d2 := 0; d2 < 4; d2++ {
				a2 := a[d2]
				if d2 == d1 || d2 == d0 || a2 > 5 {
					continue
				}
				for d3 := 0; d3 < 4; d3++ {
					a3 := a[d3]
					if d3 == d2 || d3 == d1 || d3 == d0 {
						continue
					}

					// finally we have four distinct digit and we can find the hour value
					totalTimeMinutes := (a0*10+a1)*60 + a2*10 + a3
					if totalTimeMinutes > max {
						max = totalTimeMinutes
						r[0], r[1], r[2], r[3] = a0, a1, a2, a3
					}
				}
			}
		}
	}
	if max < 0 {
		return ""
	}
	return fmt.Sprintf("%d%d:%d%d", r[0], r[1], r[2], r[3])
}

/*
Excel Sheet Column Number
Given a column title as appear in an Excel sheet, return its corresponding column number.
*/

func titleToNumber(s string) int {
	result := 0
	multiplier := 1
	for i := len(s) - 1; i >= 0; i-- {
		c := (s[i] - 'A' + 1)
		result += multiplier * int(c)
		multiplier *= 26
	}
	return result
}
