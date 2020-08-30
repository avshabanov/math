package miscleetproblems

import (
	"math"
	"math/rand"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"testing"
)

func TestSample(t *testing.T) {
	t.Logf("done; r=%d", rand.Intn(10))
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

func intMin(x, y int) int {
	if x < y {
		return x
	}
	return y
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
