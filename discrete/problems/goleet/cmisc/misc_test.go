package miscleetproblems

import (
	"math"
	"math/rand"
	"regexp"
	"sort"
	"strings"
	"testing"
)

func TestSample(t *testing.T) {
	t.Logf("done; r=%d", rand.Intn(10))
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

func intMax(x, y int) int {
	if x > y {
		return x
	}
	return y
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

type TreeNode struct {
	Val   int
	Left  *TreeNode
	Right *TreeNode
}

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
