package leet

import (
	"bytes"
	"math"
	"testing"
)

/*
Word Search
Given a 2D board and a word, find if the word exists in the grid.

The word can be constructed from letters of sequentially adjacent cell, where "adjacent" cells are those horizontally
or vertically neighboring. The same letter cell may not be used more than once.
*/

func exist(board [][]byte, word string) bool {
	if len(word) == 0 {
		return true
	}
	height := len(board)
	if height == 0 {
		return false
	}
	width := len(board[0])
	if width == 0 {
		return false
	}

	sc := boardScanner{board: board, word: word}
	for y := 0; y < height; y++ {
		for x := 0; x < width; x++ {
			if board[y][x] == word[0] && sc.recursiveExists(x, y, 1) {
				return true
			}
		}
	}

	return false
}

type boardScanner struct {
	board [][]byte
	word  string
}

func (t *boardScanner) recursiveExists(x int, y int, wordPos int) bool {
	if wordPos == len(t.word) {
		return true
	}

	result := false
	prevCh := t.board[y][x]
	t.board[y][x] = 0
	ch := t.word[wordPos]

	if y > 0 && t.board[y-1][x] == ch {
		if t.recursiveExists(x, y-1, wordPos+1) {
			result = true
			goto LEnd
		}
	}

	if y < (len(t.board)-1) && t.board[y+1][x] == ch {
		if t.recursiveExists(x, y+1, wordPos+1) {
			result = true
			goto LEnd
		}
	}

	if x > 0 && t.board[y][x-1] == ch {
		if t.recursiveExists(x-1, y, wordPos+1) {
			result = true
			goto LEnd
		}
	}

	if x < (len(t.board[0])-1) && t.board[y][x+1] == ch {
		if t.recursiveExists(x+1, y, wordPos+1) {
			result = true
			goto LEnd
		}
	}

LEnd:
	t.board[y][x] = prevCh
	return result
}

/*
Remove Linked List Elements
Remove all elements from a linked list of integers that have value val.
*/

type ListNode struct {
	Val  int
	Next *ListNode
}

func removeElements(head *ListNode, val int) *ListNode {
	root := ListNode{Next: head}
	prev := &root
	for it := prev.Next; it != nil; it = it.Next {
		if it.Val == val {
			prev.Next = it.Next
			continue
		}

		prev.Next = it
		prev = it
	}
	return root.Next
}

/*
Add Binary
Given two binary strings, return their sum (also a binary string).

The input strings are both non-empty and contains only characters 1 or 0.
*/

func addBinary(a string, b string) string {
	var buf bytes.Buffer
	ia := len(a) - 1
	ib := len(b) - 1
	carry := 0
	for ia >= 0 || ib >= 0 {
		var da, db int // current positional digits
		if ia >= 0 {
			da = charToDigit(a[ia])
			ia--
		}
		if ib >= 0 {
			db = charToDigit(b[ib])
			ib--
		}
		result := da + db + carry
		if result >= 2 {
			carry = 1
			result -= 2
		} else {
			carry = 0
		}
		buf.WriteByte(digitToChar(result))
	}
	if carry > 0 {
		buf.WriteByte(digitToChar(carry))
	}

	// reverse bytes
	bytes := buf.Bytes()
	for i := 0; i < len(bytes)/2; i++ {
		j := len(bytes) - i - 1
		bytes[i], bytes[j] = bytes[j], bytes[i]
	}

	return string(bytes)
}

func digitToChar(d int) byte {
	switch d {
	case 0:
		return '0'
	case 1:
		return '1'
	default:
		panic("digit is out of allowed range")
	}
}

func charToDigit(n byte) int {
	switch n {
	case '0':
		return 0
	case '1':
		return 1
	default:
		panic("unknown symbol")
	}
}

/*
Course Schedule II
There are a total of n courses you have to take, labeled from 0 to n-1.

Some courses may have prerequisites, for example to take course 0 you have to first take course 1, which is expressed as a pair: [0,1]

Given the total number of courses and a list of prerequisite pairs, return the ordering of courses you should take to finish all courses.

There may be multiple correct orders, you just need to return one of them. If it is impossible to finish all courses, return an empty array.
*/

type adjMatrix map[int]map[int]bool

func (t adjMatrix) put(key int, value int) {
	values, exists := t[key]
	if !exists {
		values = map[int]bool{}
		t[key] = values
	}
	values[value] = true
}

func findOrder(numCourses int, prerequisites [][]int) []int {
	// create a list of dependencies (to->from) and dependents (from->to)
	dependencies := adjMatrix{}
	dependents := adjMatrix{}
	for _, edge := range prerequisites {
		// `to` depends on `from`
		to := edge[0]
		from := edge[1]

		dependencies.put(to, from)
		dependents.put(from, to)
	}

	// fill "self-sufficient" courses, if any
	for i := 0; i < numCourses; i++ {
		_, exists := dependencies[i]
		if !exists {
			dependencies[i] = nil
		}
	}

	var result []int
	for len(result) < numCourses {

		// find dependencies that we can remove
		var toDelete []int
		for to, toDeps := range dependencies {
			if toDeps != nil && len(toDeps) > 0 {
				continue
			}

			// to-dependency depends on nothing, it can be added as a next candidate
			result = append(result, to)
			toDelete = append(toDelete, to)

			// dependents on `to` must update their own dependency lists with the exclusion of to-dependency
			fromDeps := dependents[to]
			if fromDeps == nil {
				continue
			}
			for fromDep := range fromDeps {
				// here: possible optimization is to stop iterating over range of dependencies and rather
				// form a list of next-items-to-visit, this reduces complexity to O(n).
				// all toDelete dependencies that will become empty would become next candidates for removal
				delete(dependencies[fromDep], to) // becomes empty? => we have a candidate for the next toDelete list!
			}
		}

		// if we iterated but found nothing, there is a loop, return nil
		if len(toDelete) == 0 {
			return nil
		}

		// also delete dependencies entry as we visited all we could
		for _, to := range toDelete {
			delete(dependencies, to)
		}
	}

	return result
}

func TestCourseScheduleII(t *testing.T) {

	t.Run("TestCourseScheduleII 1, 0", func(t *testing.T) {
		s := findOrder(2, [][]int{{1, 0}})
		t.Logf("1) s=%v\n", s)
	})

	t.Run("TestCourseScheduleII 2, 1, 0", func(t *testing.T) {
		s := findOrder(3, [][]int{{1, 0}, {2, 1}})
		t.Logf("2) s=%v\n", s)
	})

	t.Run("TestCourseScheduleII (10)", func(t *testing.T) {
		s := findOrder(10, [][]int{{1, 0}})
		t.Logf("2) s=%v\n", s)
	})
}

/*
Top K Frequent Elements
Given a non-empty array of integers, return the k most frequent elements.

Example 1:

Input: nums = [1,1,1,2,2,3], k = 2
Output: [1,2]
Example 2:

Input: nums = [1], k = 1
Output: [1]
Note:

You may assume k is always valid, 1 ≤ k ≤ number of unique elements.
Your algorithm's time complexity must be better than O(n log n), where n is the array's size.
It's guaranteed that the answer is unique, in other words the set of the top k frequent elements is unique.
You can return the answer in any order.
*/

func topKFrequent(nums []int, k int) []int {
	// fill out frequence map: key==number, value==frequency of occurrence
	// complexity: time=O(n), space=O(n)
	freq := map[int]int{}
	for _, num := range nums {
		freq[num] = freq[num] + 1
	}

	// fill out frequency links (counting sort)
	// complexity: time=O(n), space=O(n)
	links := make([]*freqLink, len(nums)+1)
	for num, f := range freq {
		links[f] = &freqLink{num, links[f]}
	}

	// finally fill out result off of links
	// complexity: time=O(k), space=O(k)
	result := make([]int, k)
	resultPos := 0
	for i := len(links) - 1; i >= 0 && resultPos < len(result); i-- {
		link := links[i]
		for link != nil {
			result[resultPos] = link.num
			link = link.next
			resultPos++
		}
	}

	return result
}

type freqLink struct {
	num  int
	next *freqLink
}

func TestKFreq(t *testing.T) {
	//s := topKFrequent([]int{1, 2, 2, 3, 3, 3, 4, 4, 4, 4}, 2)
	s := topKFrequent([]int{1}, 1)
	t.Logf("s=%v\n", s)
}

/*
Pow(x, n)

Implement pow(x, n), which calculates x raised to the power n (xn).
*/

func myPow(x float64, n int) float64 {
	val := math.Exp(float64(n) * math.Log(math.Abs(x)))
	if x < 0 && n%2 == 1 {
		return -val
	}
	return val
}

// below is the same as above, but without log+exp functions
func myPow2(x float64, n int) float64 {
	var multiplier float64
	if n < 0 {
		n = -n
		multiplier = 1 / x
	} else {
		multiplier = x
	}

	result := 1.0
	for n > 0 {
		if n&1 == 1 {
			result = result * multiplier
		}
		n = n >> 1
		multiplier = multiplier * multiplier
	}

	return result
}

/*
Reverse Words in a String

Given an input string, reverse the string word by word.
*/

func reverseWords(s string) string {
	buffer := make([]byte, len(s))
	lastPos := len(s)

	for pos := 0; pos < len(s); pos++ {
		ch := s[pos]
		if ch == ' ' {
			continue
		}

		endPos := pos + 1
		for endPos < len(s) {
			if s[endPos] == ' ' {
				break
			}
			endPos++
		}

		if lastPos < len(s) {
			lastPos--
			buffer[lastPos] = ' '
		}

		for i := endPos - 1; i >= pos; i-- {
			lastPos--
			buffer[lastPos] = s[i]
		}

		pos = endPos
	}

	return string(buffer[lastPos:])
}

func TestWordReversal(t *testing.T) {
	s := reverseWords("this is a comet")
	t.Logf("s=%s\n", s)
}
