package cmisc

import (
	"bytes"
	"fmt"
	"math"
	"math/bits"
	"math/rand"
	"reflect"
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
Stone Game IV
Alice and Bob take turns playing a game, with Alice starting first.

Initially, there are n stones in a pile.  On each player's turn, that player makes a move consisting of removing
any non-zero square number of stones in the pile.

Also, if a player cannot make a move, he/she loses the game.

Given a positive integer n. Return True if and only if Alice wins the game otherwise return False,
assuming both players play optimally.

Constraints:

1 <= n <= 10^5
*/

func winnerSquareGameWithBitSet(n int) bool {
	dp := newSimpleBitset(n + 1) // false: bob wins, true: alice wins
	for i := 1; i <= n; i++ {
		var aliceWins bool
		for j := 1; ; j++ {
			square := j * j
			if i-square < 0 {
				break
			}

			if !dp.Bit(i - square) {
				aliceWins = true
				break
			}
		}
		if aliceWins {
			dp.SetBit(i, true)
		}
	}
	return dp.Bit(n)
}

func winnerSquareGame(n int) bool {
	// TODO: bitset is better
	dp := make([]int, n+1) // 0: bob wins, 1: alice wins
	for i := 1; i <= n; i++ {

		var aliceWins bool
		for j := 1; ; j++ {
			square := j * j
			if i-square < 0 {
				break
			}
			if dp[i-square] == 0 {
				aliceWins = true
				break
			}
		}
		if aliceWins {
			dp[i] = 1
		}
	}
	return dp[n] == 1
}

/*
Bag of Tokens
You have an initial power of P, an initial score of 0, and a bag of tokens where tokens[i]
is the value of the ith token (0-indexed).

Your goal is to maximize your total score by potentially playing each token in one of two ways:

If your current power is at least tokens[i], you may play the ith token face up, losing tokens[i] power and gaining 1 score.
If your current score is at least 1, you may play the ith token face down, gaining tokens[i] power and losing 1 score.
Each token may be played at most once and in any order. You do not have to play all the tokens.

Return the largest possible score you can achieve after playing any number of tokens.
*/

func bagOfTokensScore(tokens []int, power int) int {
	sort.Ints(tokens)

	var score int
	for {
		// acquire as much tokens as we can
		var acquiredCount int
		for i := 0; i < len(tokens); i++ {
			if tokens[i] > power {
				break
			}
			power -= tokens[i]
			score++
			acquiredCount++
		}

		// stop, if we can't acquire tokens at the expense of trading one score for highest value token
		if acquiredCount == 0 || len(tokens) <= acquiredCount+1 || tokens[len(tokens)-1]+power < tokens[acquiredCount] {
			break
		}
		power += tokens[len(tokens)-1]
		tokens = tokens[acquiredCount : len(tokens)-1]
		score--
	}

	return score
}

func TestBagOfTokensScore1(t *testing.T) {
	t.Logf("result=%d", bagOfTokensScore([]int{6, 0, 39, 52, 45, 49, 59, 68, 42, 37}, 99))
}

func TestBagOfTokensScore2(t *testing.T) {
	t.Logf("result=%d", bagOfTokensScore([]int{1, 2, 3, 4}, 2))
}

/*
132 Pattern
Given an array of n integers nums, a 132 pattern is a subsequence of three integers
nums[i], nums[j] and nums[k] such that i < j < k and nums[i] < nums[k] < nums[j].

Return true if there is a 132 pattern in nums, otherwise, return false.

Follow up: The O(n^2) is trivial, could you come up with the O(n logn) or the O(n) solution?

Constraints:

n == nums.length
1 <= n <= 10^4
-10^9 <= nums[i] <= 10^9
*/

func find132patternOption1(nums []int) bool {
	right, max := len(nums), math.MinInt64
	for i := len(nums) - 1; i >= 0; i-- {
		if nums[i] < max {
			return true
		}
		for right < len(nums) && nums[i] > nums[right] {
			max = nums[right]
			right++
		}
		right--
		nums[right] = nums[i]
	}
	return false
}

func find132patternOption2(nums []int) bool {
	if len(nums) < 3 {
		return false
	}

	// fill out minimum elements
	mins := make([]int, len(nums))
	mins[0] = nums[0]
	for i := 1; i < len(nums); i++ {
		mins[i] = intMin(mins[i-1], nums[i])
	}

	k := len(nums)
	for i := len(nums) - 1; i >= 0; i-- {
		if nums[i] <= mins[i] {
			continue
		}
		for k < len(nums) && nums[k] <= mins[i] {
			k++
		}
		if k < len(nums) && nums[k] < nums[i] {
			return true
		}
		k--
		nums[k] = nums[i]
	}

	return false
}

/*
Minimum Depth of Binary Tree
Given a binary tree, find its minimum depth.

The minimum depth is the number of nodes along the shortest path from the root node down to the nearest leaf node.

Note: A leaf is a node with no children.
*/

func minDepth(root *TreeNode) int {
	if root == nil {
		return 0
	}
	if root.Left == nil && root.Right == nil {
		return 1
	}
	var childrenDepth int = math.MaxInt32
	if root.Left != nil {
		childrenDepth = intMin(childrenDepth, minDepth(root.Left))
	}
	if root.Right != nil {
		childrenDepth = intMin(childrenDepth, minDepth(root.Right))
	}
	return 1 + childrenDepth
}

/*
Asteroid Collision
We are given an array asteroids of integers representing asteroids in a row.

For each asteroid, the absolute value represents its size, and the sign represents its direction
(positive meaning right, negative meaning left). Each asteroid moves at the same speed.

Find out the state of the asteroids after all collisions. If two asteroids meet, the smaller one will explode.
If both are the same size, both will explode. Two asteroids moving in the same direction will never meet.

Constraints:

1 <= asteroids <= 104
-1000 <= asteroids[i] <= 1000
asteroids[i] != 0
*/

func asteroidCollision(asteroids []int) []int {
	var moveRight []int
	var result []int

	for _, a := range asteroids {
		if a > 0 {
			moveRight = append(moveRight, a)
			continue
		}

		// asteroid moves to the left, terminate all asteroids that are still moving to the right
		var exploded bool
		for len(moveRight) > 0 {
			last := moveRight[len(moveRight)-1]
			if last > -a {
				exploded = true
				break
			}

			moveRight = moveRight[0 : len(moveRight)-1] // exclude this asteroid
			if last == -a {
				exploded = true
				break
			}
		}

		if exploded {
			continue
		}

		result = append(result, a)
	}

	result = append(result, moveRight...)
	return result
}

/*
Clone Graph
Given a reference of a node in a connected undirected graph.

Return a deep copy (clone) of the graph.

Each node in the graph contains a val (int) and a list (List[Node]) of its neighbors.

class Node {
    public int val;
    public List<Node> neighbors;
}


Test case format:

For simplicity sake, each node's value is the same as the node's index (1-indexed).
For example, the first node with val = 1, the second node with val = 2, and so on.
The graph is represented in the test case using an adjacency list.
Adjacency list is a collection of unordered lists used to represent a finite graph.
Each list describes the set of neighbors of a node in the graph.
The given node will always be the first node with val = 1. You must return the copy of the given node as
a reference to the cloned graph.
*/

/*
Minimum Domino Rotations For Equal Row
In a row of dominoes, A[i] and B[i] represent the top and bottom halves of the ith domino.
(A domino is a tile with two numbers from 1 to 6 - one on each half of the tile.)

We may rotate the ith domino, so that A[i] and B[i] swap values.

Return the minimum number of rotations so that all the values in A are the same, or all the values in B are the same.

If it cannot be done, return -1.

2 <= A.length == B.length <= 2 * 104
1 <= A[i], B[i] <= 6

Constraints:

1 <= Node.val <= 100
Node.val is unique for each node.
Number of Nodes will not exceed 100.
There is no repeated edges and no self-loops in the graph.
The Graph is connected and all nodes can be visited starting from the given node.
*/

func cloneGraph(node *GraphNode) *GraphNode {
	if node == nil {
		return nil
	}

	// NB: constraint - 1 <= Node.val <= 100
	nodes := make([]*GraphNode, 100)
	var recursiveClone func(*GraphNode) *GraphNode

	recursiveClone = func(n *GraphNode) *GraphNode {
		index := n.Val - 1
		if nodes[index] != nil {
			return nodes[index]
		}

		newNode := &GraphNode{Val: n.Val}
		nodes[index] = newNode

		for _, nb := range n.Neighbors {
			newNode.Neighbors = append(newNode.Neighbors, recursiveClone(nb))
		}
		return newNode
	}

	return recursiveClone(node)
}

/* Return minimum number (-1 if not possible) of domino rotations, so that one side has all-equal numbers */

func minDominoRotations(a []int, b []int) int {
	size := len(a)
	if size == 0 || len(b) != size {
		return -1
	}

	var numFreq [6]int
	for i, ia := range a {
		numFreq[ia-1]++
		ib := b[i]
		if ia != ib {
			numFreq[ib-1]++
		}
	}

	num := -1
	for n, freq := range numFreq {
		if freq == size {
			num = n + 1
			break
		}
	}

	if num < 0 {
		return -1
	}

	var af, bf int
	for i, ia := range a {
		if ia == num {
			if ia == b[i] {
				continue
			}

			af++
		} else {
			bf++
		}
	}

	if af < bf {
		return af
	}
	return bf
}

func TestMinDominoRotations(t *testing.T) {
	t.Logf("result=%d", minDominoRotations(
		[]int{2, 1, 2, 4, 2, 2},
		[]int{5, 2, 6, 2, 3, 2},
	))
}

/*
Best Time to Buy and Sell Stock IV
You are given an integer array prices where prices[i] is the price of a given stock on the ith day.

Design an algorithm to find the maximum profit. You may complete at most k transactions.

Notice that you may not engage in multiple transactions simultaneously (i.e., you must sell the stock before you buy again).



Example 1:

Input: k = 2, prices = [2,4,1]
Output: 2
Explanation: Buy on day 1 (price = 2) and sell on day 2 (price = 4), profit = 4-2 = 2.
Example 2:

Input: k = 2, prices = [3,2,6,5,0,3]
Output: 7
Explanation: Buy on day 2 (price = 2) and sell on day 3 (price = 6), profit = 6-2 = 4.
Then buy on day 5 (price = 0) and sell on day 6 (price = 3), profit = 3-0 = 3.


Constraints:

0 <= k <= 10^9
0 <= prices.length <= 10^4
0 <= prices[i] <= 1000
*/

func maxProfitIVBruteforce(k int, prices []int) int {
	sc := maxProfitIVScanContext{k: k, prices: prices}
	sc.scan(0)
	return sc.totalMaxProfit
}

type maxProfitIVScanContext struct {
	prices         []int
	k              int
	maxProfitSoFar int
	totalMaxProfit int
}

func (t *maxProfitIVScanContext) scan(pos int) {
	if t.maxProfitSoFar > t.totalMaxProfit {
		t.totalMaxProfit = t.maxProfitSoFar // capture max profit found so far
	}
	if t.k == 0 {
		return // no more transactions possible
	}

	// save mutable context
	prevMaxProfitSoFar := t.maxProfitSoFar
	t.k--

	for j := pos; j < len(t.prices)-1; j++ {
		src, maxPrevDiff := t.prices[j], 0
		for i := j + 1; i < len(t.prices); i++ {
			diff := t.prices[i] - src
			if diff > maxPrevDiff {
				maxPrevDiff = diff                                        // there is no point trying transaction that follows bigger previous one
				t.maxProfitSoFar = prevMaxProfitSoFar + t.prices[i] - src // found one possible transaction
				t.scan(i + 1)                                             // scan right after this transaction
			}
		}
	}

	// restore context
	t.k++
	t.maxProfitSoFar = prevMaxProfitSoFar
}

//
// Optimized, DP-based solution
//

func maxProfitIVDP(k int, prices []int) int {
	// sanity check
	if k == 0 || len(prices) <= 1 {
		return 0
	}

	// normalize number of transactions
	if k > len(prices)/2 {
		k = len(prices) / 2
	}

	txs := make([]int, k*2)
	for i := 0; i < k; i++ {
		txs[i*2] = math.MinInt32
	}
	for _, p := range prices {
		txs[0] = intMax(txs[0], -p)
		for i := 1; i < len(txs); i++ {
			if i%2 == 1 {
				txs[i] = intMax(txs[i], txs[i-1]+p) // sell transaction
			} else {
				txs[i] = intMax(txs[i], txs[i-1]-p) // buy transaction
			}
		}
	}

	return txs[len(txs)-1]
}

func TestMaxProfitIVMatch1(t *testing.T) {
	testCases := []struct {
		k        int
		prices   []int
		expected int
	}{
		{k: 2, expected: 7, prices: []int{3, 2, 6, 5, 0, 3}},
		{k: 2, expected: 2, prices: []int{2, 4, 1}},
		{k: 2, expected: 7, prices: []int{6, 1, 3, 2, 4, 7}},
		{k: 1, expected: 6, prices: []int{6, 1, 3, 2, 4, 7}},
		{k: 1, expected: 37, prices: []int{0, 10, 3, 11, 5, 12, 7, 37, 0}},
		{k: 2, expected: 44, prices: []int{0, 10, 3, 11, 5, 12, 7, 37, 0}},
		{k: 3, expected: 50, prices: []int{0, 10, 3, 11, 5, 12, 7, 37, 0}},
		{k: 4, expected: 55, prices: []int{0, 10, 3, 11, 5, 12, 7, 37, 0}},
		{k: 5, expected: 55, prices: []int{0, 10, 3, 11, 5, 12, 7, 37, 0}},
	}
	//maxProfitIV := maxProfitIVBruteforce
	maxProfitIV := maxProfitIVDP
	for _, tc := range testCases {
		t.Run(fmt.Sprintf("k=%d prices=%v", tc.k, tc.prices), func(t *testing.T) {
			actual := maxProfitIV(tc.k, tc.prices)
			if tc.expected < 0 {
				t.Logf("result=%d", actual)
				return
			}
			if tc.expected != actual {
				t.Errorf("expected=%d, got=%d", tc.expected, actual)
			}
		})
	}
}

func TestMaxProfitIVMatchStress(t *testing.T) {
	result := maxProfitIVDP(29 /*orig: 29*/, []int{
		70, 4, 83, 56, 94, 72, 78, 43, 2, 86, 65, 100, 94, 56, 41, 66, 3, 33, 10, 3, 45, 94, 15, 12, 78, 60, 58, 0, 58, 15, 21, 7, 11, 41, 12, 96, 83, 77, 47,
		62, 27, 19, 40, 63, 30, 4, 77, 52, 17, 57, 21, 66, 63, 29, 51, 40, 37, 6, 44, 42, 92, 16, 64, 33, 31, 51, 36, 0, 29, 95, 92, 35, 66, 91, 19, 21, 100,
		95, 40, 61, 15, 83, 31, 55, 59, 84, 21, 99, 45, 64, 90, 25, 40, 6, 41, 5, 25, 52, 59, 61, 51, 37, 92, 90, 20, 20, 96, 66, 79, 28, 83, 60, 91, 30, 52,
		55, 1, 99, 8, 68, 14, 84, 59, 5, 34, 93, 25, 10, 93, 21, 35, 66, 88, 20, 97, 25, 63, 80, 20, 86, 33, 53, 43, 86, 53, 55, 61, 77, 9, 2, 56, 78, 43, 19,
		68, 69, 49, 1, 6, 5, 82, 46, 24, 33, 85, 24, 56, 51, 45, 100, 94, 26, 15, 33, 35, 59, 25, 65, 32, 26, 93, 73, 0, 40, 92, 56, 76, 18, 2, 45, 64, 66, 64,
		39, 77, 1, 55, 90, 10, 27, 85, 40, 95, 78, 39, 40, 62, 30, 12, 57, 84, 95, 86, 57, 41, 52, 77, 17, 9, 15, 33, 17, 68, 63, 59, 40, 5, 63, 30, 86, 57,
		5, 55, 47, 0, 92, 95, 100, 25, 79, 84, 93, 83, 93, 18, 20, 32, 63, 65, 56, 68, 7, 31, 100, 88, 93, 11, 43, 20, 13, 54, 34, 29, 90, 50, 24, 13, 44, 89,
		57, 65, 95, 58, 32, 67, 38, 2, 41, 4, 63, 56, 88, 39, 57, 10, 1, 97, 98, 25, 45, 96, 35, 22, 0, 37, 74, 98, 14, 37, 77, 54, 40, 17, 9, 28, 83, 13, 92,
		3, 8, 60, 52, 64, 8, 87, 77, 96, 70, 61, 3, 96, 83, 56, 5, 99, 81, 94, 3, 38, 91, 55, 83, 15, 30, 39, 54, 79, 55, 86, 85, 32, 27, 20, 74, 91, 99, 100,
		46, 69, 77, 34, 97, 0, 50, 51, 21, 12, 3, 84, 84, 48, 69, 94, 28, 64, 36, 70, 34, 70, 11, 89, 58, 6, 90, 86, 4, 97, 63, 10, 37, 48, 68, 30, 29, 53, 4,
		91, 7, 56, 63, 22, 93, 69, 93, 1, 85, 11, 20, 41, 36, 66, 67, 57, 76, 85, 37, 80, 99, 63, 23, 71, 11, 73, 41, 48, 54, 61, 49, 91, 97, 60, 38, 99, 8, 17,
		2, 5, 56, 3, 69, 90, 62, 75, 76, 55, 71, 83, 34, 2, 36, 56, 40, 15, 62, 39, 78, 7, 37, 58, 22, 64, 59, 80, 16, 2, 34, 83, 43, 40, 39, 38, 35, 89, 72,
		56, 77, 78, 14, 45, 0, 57, 32, 82, 93, 96, 3, 51, 27, 36, 38, 1, 19, 66, 98, 93, 91, 18, 95, 93, 39, 12, 40, 73, 100, 17, 72, 93, 25, 35, 45, 91, 78,
		13, 97, 56, 40, 69, 86, 69, 99, 4, 36, 36, 82, 35, 52, 12, 46, 74, 57, 65, 91, 51, 41, 42, 17, 78, 49, 75, 9, 23, 65, 44, 47, 93, 84, 70, 19, 22, 57,
		27, 84, 57, 85, 2, 61, 17, 90, 34, 49, 74, 64, 46, 61, 0, 28, 57, 78, 75, 31, 27, 24, 10, 93, 34, 19, 75, 53, 17, 26, 2, 41, 89, 79, 37, 14, 93, 55, 74,
		11, 77, 60, 61, 2, 68, 0, 15, 12, 47, 12, 48, 57, 73, 17, 18, 11, 83, 38, 5, 36, 53, 94, 40, 48, 81, 53, 32, 53, 12, 21, 90, 100, 32, 29, 94, 92, 83,
		80, 36, 73, 59, 61, 43, 100, 36, 71, 89, 9, 24, 56, 7, 48, 34, 58, 0, 43, 34, 18, 1, 29, 97, 70, 92, 88, 0, 48, 51, 53, 0, 50, 21, 91, 23, 34, 49, 19, 17,
		9, 23, 43, 87, 72, 39, 17, 17, 97, 14, 29, 4, 10, 84, 10, 33, 100, 86, 43, 20, 22, 58, 90, 70, 48, 23, 75, 4, 66, 97, 95, 1, 80, 24, 43, 97, 15, 38, 53,
		55, 86, 63, 40, 7, 26, 60, 95, 12, 98, 15, 95, 71, 86, 46, 33, 68, 32, 86, 89, 18, 88, 97, 32, 42, 5, 57, 13, 1, 23, 34, 37, 13, 65, 13, 47, 55, 85, 37,
		57, 14, 89, 94, 57, 13, 6, 98, 47, 52, 51, 19, 99, 42, 1, 19, 74, 60, 8, 48, 28, 65, 6, 12, 57, 49, 27, 95, 1, 2, 10, 25, 49, 68, 57, 32, 99, 24, 19, 25,
		32, 89, 88, 73, 96, 57, 14, 65, 34, 8, 82, 9, 94, 91, 19, 53, 61, 70, 54, 4, 66, 26, 8, 63, 62, 9, 20, 42, 17, 52, 97, 51, 53, 19, 48, 76, 40, 80, 6, 1,
		89, 52, 70, 38, 95, 62, 24, 88, 64, 42, 61, 6, 50, 91, 87, 69, 13, 58, 43, 98, 19, 94, 65, 56, 72, 20, 72, 92, 85, 58, 46, 67, 2, 23, 88, 58, 25, 88,
		18, 92, 46, 15, 18, 37, 9, 90, 2, 38, 0, 16, 86, 44, 69, 71, 70, 30, 38, 17, 69, 69, 80, 73, 79, 56, 17, 95, 12, 37, 43, 5, 5, 6, 42, 16, 44, 22, 62, 37,
		86, 8, 51, 73, 46, 44, 15, 98, 54, 22, 47, 28, 11, 75, 52, 49, 38, 84, 55, 3, 69, 100, 54, 66, 6, 23, 98, 22, 99, 21, 74, 75, 33, 67, 8, 80, 90, 23, 46,
		93, 69, 85, 46, 87, 76, 93, 38, 77, 37, 72, 35, 3, 82, 11, 67, 46, 53, 29, 60, 33, 12, 62, 23, 27, 72, 35, 63, 68, 14, 35, 27, 98, 94, 65, 3, 13, 48, 83,
		27, 84, 86, 49, 31, 63, 40, 12, 34, 79, 61, 47, 29, 33, 52, 100, 85, 38, 24, 1, 16, 62, 89, 36, 74, 9, 49, 62, 89,
	})
	t.Logf("result=%d", result)
}

/*
Repeated DNA Sequences

All DNA is composed of a series of nucleotides abbreviated as 'A', 'C', 'G', and 'T', for example: "ACGAATTCCG".
When studying DNA, it is sometimes useful to identify repeated sequences within the DNA.

Write a function to find all the 10-letter-long sequences (substrings) that occur more than once in a DNA molecule.

Example 1:

Input: s = "AAAAACCCCCAAAAACCCCCCAAAAAGGGTTT"
Output: ["AAAAACCCCC","CCCCCAAAAA"]
Example 2:

Input: s = "AAAAAAAAAAAAA"
Output: ["AAAAAAAAAA"]


Constraints:

0 <= s.length <= 105
s[i] is 'A', 'C', 'G', or 'T'.
*/

func findRepeatedDnaSequences(s string) []string {
	var root dnaTrieNode
	var result []string
	var cursors [dnaTrieSequenceLen]*dnaTrieCursor
	for i := 0; i < len(s); i++ {
		dnaCode := packedDnaCode(s[i])
		firstAssigned := false
		for j, c := range cursors {
			if c == nil {
				if firstAssigned {
					continue
				}
				firstAssigned = true
				c = &dnaTrieCursor{it: &root}
				cursors[j] = c
			}

			nextChild := c.it.children[dnaCode]
			if nextChild == nil {
				nextChild = &dnaTrieNode{}
				c.it.children[dnaCode] = nextChild
			}
			c.it = nextChild
			c.len++

			if c.len == dnaTrieSequenceLen {
				if nextChild.count == 1 {
					result = append(result, s[i-dnaTrieSequenceLen+1:i+1])
				}
				nextChild.count++
				c.it = &root
				c.len = 0
			}
		}
	}
	return result
}

type dnaTrieCursor struct {
	it  *dnaTrieNode
	len int
}

type dnaTrieNode struct {
	children [4]*dnaTrieNode
	count    int // TODO: optimize: count is needed only for a union node
}

const dnaTrieSequenceLen = 10

func packedDnaCode(b byte) uint {
	switch b {
	case 'A':
		return 0
	case 'C':
		return 1
	case 'G':
		return 2
	case 'T':
		return 3
	}
	panic("unknown DNA char")
}

const dnaSequenceMask uint32 = (1 << (2 * dnaTrieSequenceLen)) - 1

// alt solution using bit masks
func findRepeatedDnaSequences2(s string) []string {
	if len(s) <= dnaTrieSequenceLen {
		return nil
	}

	var dna uint32 // 2 bits * 10 = 20 bits
	for i := 0; i < dnaTrieSequenceLen-1; i++ {
		dna = dna << 2
		dna |= uint32(packedDnaCode(s[i]))
	}

	var result []string
	dnaMap := map[uint32]int{}
	for i := dnaTrieSequenceLen - 1; i < len(s); i++ {
		dna = ((dna << 2) | uint32(packedDnaCode(s[i]))) & dnaSequenceMask
		count := dnaMap[dna]
		dnaMap[dna] = count + 1
		if count == 1 {
			result = append(result, s[i-dnaTrieSequenceLen+1:i+1])
		}
	}

	return result
}

func TestRepeatedDnaSequence(t *testing.T) {
	t.Logf("result=%v", findRepeatedDnaSequences2("AAAAACCCCCAAAAACCCCCCAAAAAGGGTTT"))
	t.Logf("result=%v", findRepeatedDnaSequences2("AAAAAAAAAAAAA"))
}

/*
Write an efficient algorithm that searches for a value in an m x n matrix. This matrix has the following properties:

Integers in each row are sorted from left to right.
The first integer of each row is greater than the last integer of the previous row.

Constraints:

m == matrix.length
n == matrix[i].length
0 <= m, n <= 100
-10^4 <= matrix[i][j], target <= 10^4
*/

func searchMatrix(matrix [][]int, target int) bool {
	if len(matrix) == 0 || len(matrix[0]) == 0 {
		return false
	}
	height, width := len(matrix), len(matrix[0])
	len := height * width
	index := sort.Search(len, func(pos int) bool {
		h := pos / width
		w := pos % width
		e := matrix[h][w]
		return e >= target
	})
	if index < len && matrix[index/width][index%width] == target {
		return true
	}
	return false
}

/*
Given an array, rotate the array to the right by k steps, where k is non-negative.

Follow up:

Try to come up as many solutions as you can, there are at least 3 different ways to solve this problem.
Could you do it in-place with O(1) extra space?


Example 1:

Input: nums = [1,2,3,4,5,6,7], k = 3
Output: [5,6,7,1,2,3,4]
Explanation:
rotate 1 steps to the right: [7,1,2,3,4,5,6]
rotate 2 steps to the right: [6,7,1,2,3,4,5]
rotate 3 steps to the right: [5,6,7,1,2,3,4]
Example 2:

Input: nums = [-1,-100,3,99], k = 2
Output: [3,99,-1,-100]
Explanation:
rotate 1 steps to the right: [99,-1,-100,3]
rotate 2 steps to the right: [3,99,-1,-100]


Constraints:

1 <= nums.length <= 2 * 10^4
-2^31 <= nums[i] <= 2^31 - 1
0 <= k <= 10^5
*/

func rotateArr(nums []int, k int) {
	if k == 0 || len(nums) <= 1 {
		return
	}
	k = k % len(nums)
	gcd := intGcd(k, len(nums))
	for startPos := 0; startPos < gcd; startPos++ {
		pos, nextElement := startPos, nums[startPos]
		for {
			pos = (pos + k) % len(nums)
			nextElement, nums[pos] = nums[pos], nextElement
			if pos == startPos {
				break
			}
		}
	}
}

func TestRotateArr1(t *testing.T) {
	testCases := []struct {
		src      []int
		k        int
		expected []int
	}{
		{src: []int{1, 2, 3}, k: 1, expected: []int{3, 1, 2}},
		{src: []int{1, 2, 3}, k: 2, expected: []int{2, 3, 1}},
		{src: []int{1, 2, 3}, k: 5, expected: []int{2, 3, 1}},
		{src: []int{1, 2, 3}, k: 3, expected: []int{1, 2, 3}},
		{src: []int{1, 2, 3, 4}, k: 2, expected: []int{3, 4, 1, 2}},
	}
	for _, tc := range testCases {
		t.Run(fmt.Sprintf("rotate arr %v for k=%d", tc.src, tc.k), func(t *testing.T) {
			rotateArr(tc.src, tc.k)
			if !reflect.DeepEqual(tc.src, tc.expected) {
				t.Errorf("unexpected rotation product=%v", tc.src)
			}
		})
	}
}

/*
https://leetcode.com/explore/challenge/card/october-leetcoding-challenge/560/week-2-october-8th-october-14th/3494/

Maximize sum for an array given that you can NEVER pick two adjacent indices for your elements that constitute the sum.
Array is also circular, meaning that first and last elements are considered adjacent (== can't be picked up).
*/

func rob2(nums []int) int {
	if len(nums) == 1 {
		return nums[0] // TODO: optimize this along with two passes that we do below
	}
	var m0, m1 int
	var n0, n1 int
	for i := 0; i < len(nums)-1; i++ {
		m0, m1 = intMax(m0, m1), intMax(m1, m0+nums[i])
		n0, n1 = intMax(n0, n1), intMax(n1, n0+nums[i+1])
	}
	return intMax(m1, n1)
}

/*
Sort List
Given the head of a linked list, return the list after sorting it in ascending order.
Follow up: Can you sort the linked list in O(n logn) time and O(1) memory (i.e. constant space)?

Constraints:

The number of nodes in the list is in the range [0, 5 * 104].
-10^5 <= Node.val <= 10^5
*/

// sortList sorts list in ascending order using O(1) memory using insertion sort
// best case runtime: O(n), worst case: O(n^2)
func sortList(head *ListNode) *ListNode {
	var prev, next *ListNode
	for i := head; i != nil; i = next {
		// reverse list inplace
		next = i.Next
		i.Next = prev
		prev = i

		for j := i; j != nil; j = j.Next {
			jnext := j.Next
			if jnext == nil || jnext.Val >= j.Val {
				break
			}
			jnext.Val, j.Val = j.Val, jnext.Val
		}
	}
	return prev
}

func sortListUsingMergeSort(head *ListNode) *ListNode {
	if head == nil || head.Next == nil {
		return head // nil or single-element list is by-default sorted
	}

	lists, listpos := [2]*ListNode{}, 0
	for i := head; i != nil; {
		next := i.Next
		i.Next, lists[listpos] = lists[listpos], i
		listpos, i = (listpos+1)%2, next
	}

	lists[0] = sortListUsingMergeSort(lists[0])
	lists[1] = sortListUsingMergeSort(lists[1])

	return mergeSortedLists(lists)
}

func mergeSortedLists(lists [2]*ListNode) *ListNode {
	var result ListNode
	resultlast := &result
	for lists[0] != nil && lists[1] != nil {
		var pos int
		if lists[0].Val > lists[1].Val {
			pos = 1
		}
		next := lists[pos].Next

		resultlast.Next = lists[pos]
		lists[pos].Next = nil
		resultlast = lists[pos]

		lists[pos] = next
	}
	for i := 0; i < 2; i++ {
		for j := lists[i]; j != nil; {
			next := j.Next

			resultlast.Next = j
			j.Next = nil
			resultlast = j

			j = next
		}
	}
	return result.Next
}

func TestSortList(t *testing.T) {
	l := newList(5, 1, 4, 2, 3)
	//l = sortList(l)
	l = sortListUsingMergeSort(l)
	t.Logf("result=%s", l.String())
}

/*
Return true, if one string could be made equal to the other by swapping two chars at distinct positions.
*/

func buddyStrings(a, b string) bool {
	if len(a) != len(b) {
		return false
	}

	var diffPos []int
	freq := [26]int{}
	for i := 0; i < len(a); i++ {
		freq[a[i]-'a']++
		if a[i] != b[i] {
			if len(diffPos) >= 2 {
				return false
			}
			diffPos = append(diffPos, i)
		}
	}

	if len(diffPos) == 0 {
		for _, f := range freq {
			if f > 1 {
				return true
			}
		}
		return false
	} else if len(diffPos) != 2 {
		return false
	}

	if b[diffPos[1]] != a[diffPos[0]] || b[diffPos[0]] != a[diffPos[1]] {
		return false
	}

	return true
}

func TestBuddyStrings(t *testing.T) {
	t.Logf("result=%t", buddyStrings("ab", "ca"))
}

/*
Remove Duplicate Letters
Given a string s, remove duplicate letters so that every letter appears once and only once.
You must make sure your result is the smallest in lexicographical order among all possible results.

Constraints:

1 <= s.length <= 104
s consists of lowercase English letters.
*/

func removeDuplicateLetters3(s string) string {
	r := newRdlFinderContext(s)
	r.scan(0, 0)
	// normalize result
	for i := range r.result {
		r.result[i] += 'a'
	}
	return string(r.result)
}

type rdlFinderContext struct {
	freq      [26]int
	mask      int32
	bs        []byte
	candidate []byte
	result    []byte
}

func newRdlFinderContext(s string) *rdlFinderContext {
	var r rdlFinderContext

	r.bs = make([]byte, len(s)) // fill out the frequencies and initialize character presence bitmask
	var uniqueCharCount int
	for i := 0; i < len(s); i++ {
		idx := s[i] - 'a'
		r.bs[i] = idx
		if 0 == r.mask&(1<<idx) {
			uniqueCharCount++ // compute number of unique characters
			r.mask |= (1 << idx)
		}
		r.freq[idx] = r.freq[idx] + 1 // compute character frequencies
	}

	r.candidate = make([]byte, uniqueCharCount)

	return &r
}

func (r *rdlFinderContext) scan(resultPos int, bsPos int) {
	if resultPos >= len(r.candidate) {
		// we've found a candidate
		if r.result == nil || bytes.Compare(r.candidate, r.result) < 0 {
			r.result = append([]byte{}, r.candidate...)
		}
		return
	}

	var charIndex byte // skip this character until we get something that we can take into an account
	for ; ; bsPos++ {
		charIndex = r.bs[bsPos]
		if 0 != r.mask&(1<<charIndex) {
			break
		}
	}

	// capture current values
	oldFreq, oldMask := r.freq[charIndex], r.mask

	newFreq := oldFreq - 1
	r.freq[charIndex] = newFreq // update frequencies
	if newFreq > 0 && 0 != r.mask&((1<<charIndex)-1) {
		r.scan(resultPos, bsPos+1) // try continuing without this character added if this is not the smallest char
	}

	r.mask &= ^(1 << charIndex)
	r.candidate[resultPos] = charIndex
	r.scan(resultPos+1, bsPos+1) // try continuing with this character added

	// restore old values
	r.freq[charIndex], r.mask = oldFreq, oldMask
}

func removeDuplicateLetters1(s string) string {
	lastIndices := [26]int{} // tracks last indices for each unique char
	for i := 0; i < len(s); i++ {
		lastIndices[s[i]-'a'] = i
	}

	var stack []byte  // tracks constructed string (smaller indices in stack == smaller indices in the result string)
	var visited int32 // tracks if certain character has been already seen (added to stack)
	for i := 0; i < len(s); i++ {
		charIndex := s[i] - 'a'
		if 0 != visited&(1<<charIndex) { // if visited[charIndex]
			continue
		}
		for len(stack) > 0 {
			peek := stack[len(stack)-1]
			if peek <= charIndex || i >= lastIndices[peek] {
				break
			}
			stack = stack[0 : len(stack)-1] // stack.pop()
			visited &= ^(1 << peek)         // visited[peek] = false
		}
		stack = append(stack, charIndex) // stack.push(charIndex)
		visited |= (1 << charIndex)      // visited[charIndex] = true
	}

	var sb []byte
	for i := 0; i < len(stack); i++ {
		sb = append(sb, stack[i]+'a') // sb <- reverse(stack)
	}
	return string(sb)
}

func TestRemoveDuplicateChars(t *testing.T) {
	testCases := []struct{ src, expected string }{
		{src: "yioccqiorhtoslwlvfgzycahonecugtatbyphpuunwvaalcpndabyldkdtzfjlgwqk", expected: "ciorhsaebpunvdyktzfjlgwq"},
		{src: "stswat", expected: "stwa"},
		{src: "zbdcndazbc", expected: "bcndaz"},
		{src: "mitnlruhznjfyzmtmfnstsxwktxlboxutbic", expected: "ilrhjfyzmnstwkboxuc"},
		{src: "thesqtitxyetpxloeevdeqifkz", expected: "hesitxyplovdqfkz"},
		{src: "acqbecb", expected: "acqbe"},
		{src: "acqbecq", expected: "abecq"},
		{src: "abacb", expected: "abc"},
		{src: "bcabc", expected: "abc"},
		{src: "cbacdcbc", expected: "acdb"},
		{src: "cbacdcbcd", expected: "abcd"},
	}
	for _, tc := range testCases {
		t.Run(fmt.Sprintf("remove duplicate chars for %s", tc.src), func(t *testing.T) {
			actual := removeDuplicateLetters1(tc.src)
			if actual != tc.expected {
				t.Errorf("mismatch: actual=%s, expected=%s", actual, tc.expected)
			}
		})
	}
}

/*
Minimum Number of Arrows to Burst Balloons
There are some spherical balloons spread in two-dimensional space. For each balloon, provided input is the start and
end coordinates of the horizontal diameter. Since it's horizontal, y-coordinates don't matter, and hence the
x-coordinates of start and end of the diameter suffice. The start is always smaller than the end.

An arrow can be shot up exactly vertically from different points along the x-axis. A balloon with xstart and xend bursts
by an arrow shot at x if xstart ≤ x ≤ xend. There is no limit to the number of arrows that can be shot.
An arrow once shot keeps traveling up infinitely.

Given an array points where points[i] = [xstart, xend], return the minimum number of arrows
that must be shot to burst all balloons.

Constraints:

0 <= points.length <= 10^4
points.length == 2
-2^31 <= xstart < xend <= 2^31 - 1
*/

func findMinArrowShots(points [][]int) int {
	if len(points) == 0 {
		return 0
	}
	sort.Slice(points, func(i, j int) bool { return points[i][0] < points[j][0] })
	count, itEnd := 1, points[0][1]
	for i := 1; i < len(points); i++ {
		point := points[i]
		if point[0] <= itEnd {
			itEnd = intMin(itEnd, point[1])
		} else {
			count++
			itEnd = point[1]
		}
	}
	return count
}

func TestFindMinArrowShots(t *testing.T) {
	t.Logf("result=%d", findMinArrowShots([][]int{{2, 3}, {2, 3}}))
}

/*
Serialize and Deserialize BST

Solution
Serialization is converting a data structure or object into a sequence of bits so that it can be stored in a file
or memory buffer, or transmitted across a network connection link to be reconstructed later in the same or
another computer environment.

Design an algorithm to serialize and deserialize a binary search tree. There is no restriction on how your
serialization/deserialization algorithm should work. You need to ensure that a binary search tree can be serialized
to a string, and this string can be deserialized to the original tree structure.

The encoded string should be as compact as possible.

Constraints:

The number of nodes in the tree is in the range [0, 104].
0 <= Node.val <= 104
The input tree is guaranteed to be a binary search tree.
*/

type lcCodec struct {
}

func lcConstructor() lcCodec {
	return lcCodec{}
}

func (t *lcCodec) serialize(root *TreeNode) string {
	var elements []string
	var recMarshal func(n *TreeNode) int
	recMarshal = func(n *TreeNode) int {
		if n == nil {
			return -1
		}
		p := len(elements)
		elements = append(elements, "")
		leftPos := recMarshal(n.Left)
		rightPos := recMarshal(n.Right)
		elements[p] = fmt.Sprintf("%d,%d,%d", n.Val, leftPos, rightPos)
		return p
	}
	recMarshal(root)
	return strings.Join(elements, ";")
}

func (t *lcCodec) deserialize(data string) *TreeNode {
	if len(data) == 0 {
		return nil
	}
	packedNodes := strings.Split(data, ";")
	nodeArr := make([]*TreeNode, len(packedNodes))
	for i := range nodeArr {
		nodeArr[i] = &TreeNode{}
	}

	var err error
	for i, node := range nodeArr {
		values := strings.Split(packedNodes[i], ",")
		node.Val, err = strconv.Atoi(values[0])
		if err != nil {
			panic(err)
		}

		var leftIndex, rightIndex int

		leftIndex, err = strconv.Atoi(values[1])
		if err != nil {
			panic(err)
		}

		rightIndex, err = strconv.Atoi(values[2])
		if err != nil {
			panic(err)
		}

		if leftIndex >= 0 {
			node.Left = nodeArr[leftIndex]
		}

		if rightIndex >= 0 {
			node.Right = nodeArr[rightIndex]
		}
	}

	return nodeArr[0]
}

/*
Binary Search
Given a sorted (in ascending order) integer array nums of n elements and a target value,
write a function to search target in nums. If target exists, then return its index, otherwise return -1.

Note:

You may assume that all elements in nums are unique.
n will be in the range [1, 10000].
The value of each element in nums will be in the range [-9999, 9999].
*/

func search(nums []int, target int) int {
	for left, right := 0, len(nums)-1; left <= right; {
		mid := left + (right-left)/2
		if nums[mid] == target {
			return mid
		} else if nums[mid] > target {
			right = mid - 1
			continue
		}
		left = mid + 1
	}
	return -1
}

/*
Rotate List
Given a linked list, rotate the list to the right by k places, where k is non-negative.
*/

func rotateRight(head *ListNode, k int) *ListNode {
	var len int
	var last *ListNode
	for n := head; n != nil; n = n.Next {
		len++
		last = n
	}
	if len == 0 {
		return nil // this is an empty list
	}

	k %= len
	if k == 0 {
		return head // no rotation is needed
	}

	// rotation is needed and it suffices to set up a connection between last and first node
	// and break connection pointing to the now-first node
	last.Next = head
	it := head
	headPredOffset := len - k - 1
	for i := 0; i < headPredOffset; i++ {
		it = it.Next
	}

	newHead := it.Next
	it.Next = nil

	return newHead
}

func TestRotateRight1(t *testing.T) {
	l := newList(0, 1, 2)
	lStr := l.String()
	l = rotateRight(l, 1)
	t.Logf("src=%s, result=%s", lStr, l.String())
}

func TestRotateRight2(t *testing.T) {
	l := newList(1, 2)
	lStr := l.String()
	l = rotateRight(l, 1)
	t.Logf("src=%s, result=%s", lStr, l.String())
}

/*
Insert into a Binary Search Tree
You are given the root node of a binary search tree (BST) and a value to insert into the tree.
Return the root node of the BST after the insertion.
It is guaranteed that the new value does not exist in the original BST.

Notice that there may exist multiple valid ways for the insertion, as long as the tree remains a BST after insertion.
You can return any of them.

Constraints:

The number of nodes in the tree will be in the range [0, 104].
-108 <= Node.val <= 108
All the values Node.val are unique.
-108 <= val <= 108
It's guaranteed that val does not exist in the original BST.
*/

func insertIntoBST(root *TreeNode, val int) *TreeNode {
	pp := &root
	for n := root; n != nil; n = *pp {
		if val > n.Val {
			pp = &n.Right
		} else {
			pp = &n.Left //< use constraint: `All the values Node.val are unique.`
		}
	}
	*pp = &TreeNode{Val: val}
	return root
}

func TestInsertBST(t *testing.T) {
	n := insertIntoBST(nil, 1)
	t.Logf("result=%d", n.Val)
}

/*
Complement of Base 10 Integer
Every non-negative integer N has a binary representation.  For example, 5 can be represented as "101" in binary,
11 as "1011" in binary, and so on.  Note that except for N = 0, there are no leading zeroes in any binary representation.

The complement of a binary representation is the number in binary you get when changing every 1 to a 0 and 0 to a 1.
For example, the complement of "101" in binary is "010" in binary.

For a given number N in base-10, return the complement of it's binary representation as a base-10 integer.

Example 1:

Input: 5
Output: 2
Explanation: 5 is "101" in binary, with complement "010" in binary, which is 2 in base-10.
Example 2:

Input: 7
Output: 0
Explanation: 7 is "111" in binary, with complement "000" in binary, which is 0 in base-10.
Example 3:

Input: 10
Output: 5
Explanation: 10 is "1010" in binary, with complement "0101" in binary, which is 5 in base-10.

Note:

0 <= N < 10^9
This question is the same as 476: https://leetcode.com/problems/number-complement/
*/

func bitwiseComplement(n int) int {
	if n <= 0 {
		return 1
	}

	u, b := uint(n), uint(1)
	for b < u {
		b <<= 1
	}

	return int((^u) & (b - 1))
}

/*
Remove Covered Intervals
Given a list of intervals, remove all intervals that are covered by another interval in the list.

Interval [a,b) is covered by interval [c,d) if and only if c <= a and b <= d.

After doing so, return the number of remaining intervals.



Example 1:

Input: intervals = [[1,4],[3,6],[2,8]]
Output: 2
Explanation: Interval [3,6] is covered by [2,8], therefore it is removed.
Example 2:

Input: intervals = [[1,4],[2,3]]
Output: 1
Example 3:

Input: intervals = [[0,10],[5,12]]
Output: 2
Example 4:

Input: intervals = [[3,10],[4,10],[5,11]]
Output: 2
Example 5:

Input: intervals = [[1,2],[1,4],[3,4]]
Output: 1


Constraints:

1 <= intervals.length <= 1000
intervals[i].length == 2
0 <= intervals[i][0] < intervals[i][1] <= 10^5
All the intervals are unique.
*/

type coveredIntervals [][]int

func (p coveredIntervals) Len() int { return len(p) }
func (p coveredIntervals) Less(i, j int) bool {
	lhs, rhs := p[i], p[j]
	if lhs[0] < rhs[0] {
		return true
	} else if lhs[0] == rhs[0] {
		if lhs[1] > rhs[1] {
			return true
		}
	}
	return false
}
func (p coveredIntervals) Swap(i, j int) { p[i], p[j] = p[j], p[i] }

func removeCoveredIntervals(intervals [][]int) int {
	sort.Sort(coveredIntervals(intervals))
	farthestY := -1
	removed := 0
	for _, i := range intervals {
		//fmt.Printf("[%d, %d], ", i[0], i[1])
		if farthestY >= i[1] {
			removed++
			continue
		}
		farthestY = i[1]
	}
	//fmt.Println()
	return len(intervals) - removed
}

func TestCoveredIntervals(t *testing.T) {
	t.Logf("result=%d", removeCoveredIntervals([][]int{
		{3, 6}, {1, 4}, {2, 5}, {2, 8},
	}))
}

func TestCoveredIntervals1(t *testing.T) {
	testCases := []struct {
		intervals [][]int
		expected  int
	}{
		{intervals: [][]int{{3, 6}, {1, 4}, {2, 5}, {2, 8}}, expected: 2},
		{intervals: [][]int{{1, 4}, {3, 6}, {2, 8}}, expected: 2},
		{intervals: [][]int{{1, 4}, {2, 3}}, expected: 1},
		{intervals: [][]int{{0, 10}, {5, 12}}, expected: 2},
		{intervals: [][]int{{5, 8}, {0, 10}}, expected: 1},
	}

	for _, tc := range testCases {
		t.Run(fmt.Sprintf("removeCoveredIntervals(%v) -> %d", tc.intervals, tc.expected), func(t *testing.T) {
			actual := removeCoveredIntervals(tc.intervals)
			if actual != tc.expected {
				t.Errorf("actual=%d, expected=%d", actual, tc.expected)
			}
		})
	}
}

/*
K-diff Pairs in an Array
Given an array of integers nums and an integer k, return the number of unique k-diff pairs in the array.

A k-diff pair is an integer pair (nums[i], nums[j]), where the following are true:

0 <= i, j < nums.length
i != j
a <= b
b - a == k


Example 1:

Input: nums = [3,1,4,1,5], k = 2
Output: 2
Explanation: There are two 2-diff pairs in the array, (1, 3) and (3, 5).
Although we have two 1s in the input, we should only return the number of unique pairs.
Example 2:

Input: nums = [1,2,3,4,5], k = 1
Output: 4
Explanation: There are four 1-diff pairs in the array, (1, 2), (2, 3), (3, 4) and (4, 5).
Example 3:

Input: nums = [1,3,1,5,4], k = 0
Output: 1
Explanation: There is one 0-diff pair in the array, (1, 1).
Example 4:

Input: nums = [1,2,4,4,3,3,0,9,2,3], k = 3
Output: 2
Example 5:

Input: nums = [-1,-2,-3], k = 1
Output: 2


Constraints:

1 <= nums.length <= 104
-107 <= nums[i] <= 107
0 <= k <= 107
*/

func findPairs(nums []int, k int) int {
	m := map[int]int{}
	for _, num := range nums {
		m[num]++
	}

	result := 0
	for n := range m {
		prev := n - k
		count := m[prev]
		if k == 0 {
			if count > 1 {
				result++
			}
			continue
		}

		if count > 0 {
			result++
		}
	}

	return result
}

func TestFindPairs(t *testing.T) {
	t.Logf("result=%d", findPairs([]int{3, 1, 4, 1, 5}, 2))
}

/*
Combination Sum
Given an array of distinct integers candidates and a target integer target, return a list of all unique combinations
of candidates where the chosen numbers sum to target. You may return the combinations in any order.

The same number may be chosen from candidates an unlimited number of times. Two combinations are unique
if the frequency of at least one of the chosen numbers is different.

Constraints:

1 <= candidates.length <= 30
1 <= candidates[i] <= 200
All elements of candidates are distinct.
1 <= target <= 500
*/

func combinationSum(candidates []int, target int) [][]int {
	var currentTarget int
	var currentCombination []int
	var combinations [][]int
	var finder func(int)

	finder = func(pos int) {
		currentCombinationLen := len(currentCombination)
		prevTarget := currentTarget

		defer func() {
			currentTarget = prevTarget
			currentCombination = currentCombination[0:currentCombinationLen]
		}()

		for num := candidates[pos]; ; {
			currentTarget += num
			if currentTarget > target {
				return // we're exceeding domain, no need to seek further
			}

			if currentTarget == target {
				destCombination := append([]int{num}, currentCombination...)
				combinations = append(combinations, destCombination)
				return // found resultant combination, no need to seek further
			}

			currentCombination = append(currentCombination, num)
			for newPos := pos + 1; newPos < len(candidates); newPos++ {
				finder(newPos)
			}
		}
	}

	for i := 0; i < len(candidates); i++ {
		finder(i)
	}

	return combinations
}

func TestCombinationSum1(t *testing.T) {
	testCases := []struct {
		arr    []int
		target int
	}{
		{arr: []int{2, 3, 5}, target: 8},
		{arr: []int{2, 3, 5}, target: 7},
		{arr: []int{1}, target: 1},
		{arr: []int{1}, target: 2},
		{arr: []int{2}, target: 1},
	}

	for i, tc := range testCases {
		if i > 100 {
			return
		}
		t.Run(fmt.Sprintf("combination sum for arr=%v and target=%d", tc.arr, tc.target), func(t *testing.T) {
			result := combinationSum(tc.arr, tc.target)
			t.Logf("result=%v", result)
		})
	}
}

/*
Number of Recent Calls
You have a RecentCounter class which counts the number of recent requests within a certain time frame.

Implement the RecentCounter class:

RecentCounter() Initializes the counter with zero recent requests.
int ping(int t) Adds a new request at time t, where t represents some time in milliseconds, and returns the
number of requests that has happened in the past 3000 milliseconds (including the new request).
Specifically, return the number of requests that have happened in the inclusive range [t - 3000, t].
It is guaranteed that every call to ping uses a strictly larger value of t than the previous call.

Example 1:

Input
["RecentCounter", "ping", "ping", "ping", "ping"]
[[], [1], [100], [3001], [3002]]
Output
[null, 1, 2, 3, 3]

Explanation
RecentCounter recentCounter = new RecentCounter();
recentCounter.ping(1);     // requests = [1], range is [-2999,1], return 1
recentCounter.ping(100);   // requests = [1, 100], range is [-2900,100], return 2
recentCounter.ping(3001);  // requests = [1, 100, 3001], range is [1,3001], return 3
recentCounter.ping(3002);  // requests = [1, 100, 3001, 3002], range is [2,3002], return 3

Constraints:

1 <= t <= 104
Each test case will call ping with strictly increasing values of t.
At most 104 calls will be made to ping.
*/

type lrcRecentCounter struct {
	list  *lrcRequest
	count int
}

type lrcRequest struct {
	time int
	next *lrcRequest
	prev *lrcRequest
}

func (t *lrcRequest) String() string {
	return fmt.Sprintf("(%d)", t.time)
}

func lrcConstructor() lrcRecentCounter {
	var t lrcRecentCounter
	var head lrcRequest
	h := &head
	h.next, h.prev, t.list = h, h, h
	h.time = math.MinInt32
	return t
}

const lrcTimeBound = 3000

func (t *lrcRecentCounter) Ping(time int) int {
	// prune old values
	h := t.list
	for threshold := time - lrcTimeBound; h.next != h && h.next.time < threshold; {
		nn := h.next.next
		nn.prev, h.next = h, nn
		t.count--
	}
	// insert new value
	newRequest := &lrcRequest{time: time, next: h, prev: h.prev}
	h.prev.next = newRequest
	h.prev = newRequest
	t.count++
	return t.count
}

func TestRecentCounter1(t *testing.T) {
	lrc := lrcConstructor()
	timings := []int{1, 100, 3001, 3002}
	for i, time := range timings {
		t.Logf("%2d: Ping(%d) = %d", i, time, lrc.Ping(time))
	}
}

/*
First Missing Positive
Given an unsorted integer array, find the smallest missing positive integer.

Example 1:

Input: [1,2,0]
Output: 3
Example 2:

Input: [3,4,-1,1]
Output: 2
Example 3:

Input: [7,8,9,11,12]
Output: 1
Follow up:

Your algorithm should run in O(n) time and uses constant extra space.
*/

func firstMissingPositive(nums []int) int {
	// rearrange numbers
	for _, num := range nums {
		for targetPos := num - 1; targetPos >= 0 && targetPos < len(nums); {
			otherNum := nums[targetPos]
			if otherNum == num {
				break // ignore duplicates
			}
			nums[targetPos] = num // put number on the appropriate position
			targetPos = otherNum - 1
			num = otherNum
		}
	}

	// now find what's missing
	last := 0
	for ; last < len(nums); last++ {
		expectedNum := last + 1
		if nums[last] != expectedNum {
			return expectedNum
		}
	}

	return last + 1
}

/*
Word Break
Given a non-empty string s and a dictionary wordDict containing a list of non-empty words, determine if s can be
segmented into a space-separated sequence of one or more dictionary words.

Note:

The same word in the dictionary may be reused multiple times in the segmentation.
You may assume the dictionary does not contain duplicate words.
Example 1:

Input: s = "leetcode", wordDict = ["leet", "code"]
Output: true
Explanation: Return true because "leetcode" can be segmented as "leet code".
Example 2:

Input: s = "applepenapple", wordDict = ["apple", "pen"]
Output: true
Explanation: Return true because "applepenapple" can be segmented as "apple pen apple".
             Note that you are allowed to reuse a dictionary word.
Example 3:

Input: s = "catsandog", wordDict = ["cats", "dog", "sand", "and", "cat"]
Output: false
*/

func wordBreak(s string, wordDict []string) bool {
	var prefixTree wordPrefixTree
	prefixTree.init(wordDict)
	return prefixTree.wordBreak(s)
}

type wordPrefixTreeNode struct {
	children map[byte]*wordPrefixTreeNode
	fullWord bool
}

func newWordPrefixTreeNode() *wordPrefixTreeNode {
	return &wordPrefixTreeNode{children: map[byte]*wordPrefixTreeNode{}}
}

type wordPrefixTree struct {
	rootNode *wordPrefixTreeNode
}

func (t *wordPrefixTree) wordBreak(s string) bool {
	posStack := make([]int, len(s)+1)
	posStackLen := 1 // => posStack = {0}

	visitedPositions := map[int]bool{}

	for count := 1; posStackLen > 0; count-- {
		n := t.rootNode

		// pop next element
		posStackLen--
		pos := posStack[posStackLen]
		visitedPositions[pos] = true

		//fmt.Printf("pos = %d\n", pos)

		for i := pos; i < len(s); i++ {
			nextNode, exists := n.children[s[i]]
			if !exists {
				goto NextBranch
			}

			if nextNode.fullWord {
				nextPos := i + 1
				if !visitedPositions[nextPos] {
					// only add predecessor position if we didn't visit it already
					posStack[posStackLen] = nextPos // record next position that we can start from
					posStackLen++
				}
			}

			n = nextNode
		}

		if n.fullWord {
			return true
		}
	NextBranch:
	}

	return false
}

func (t *wordPrefixTree) bootstrap(wordDict []string) map[string]*wordPrefixTreeNode {
	result := map[string]*wordPrefixTreeNode{}

	t.rootNode = newWordPrefixTreeNode()
	for _, word := range wordDict {
		if len(word) == 0 {
			continue
		}

		n := t.rootNode
		for i := 0; i < len(word); i++ {
			ch := word[i]

			nextNode, exists := n.children[ch]
			if !exists {
				nextNode = newWordPrefixTreeNode()
				n.children[ch] = nextNode
			}
			n = nextNode
		}
		n.fullWord = true
		result[word] = n
	}

	return result
}

func (t *wordPrefixTree) init(wordDict []string) {
	wordMap := t.bootstrap(wordDict)

	// re-bootstrap trie until we have composite words
	for hasCompositeWords := true; hasCompositeWords; {

		hasCompositeWords = false

		for i, word := range wordDict {
			lexeme, exists := wordMap[word]
			if !exists {
				continue
			}

			lexeme.fullWord = false
			if t.wordBreak(word) {
				//fmt.Printf("prune word '%s'\n", word)
				wordDict[i] = ""
				hasCompositeWords = true
				continue
			}
			lexeme.fullWord = true
		}

		if hasCompositeWords {
			// re-bootstrap the dictionary
			wordMap = t.bootstrap(wordDict)
		}
	}
}

func TestWordBreak1(t *testing.T) {
	t.Logf("result=%t", wordBreak("aaaaaaaa", []string{"a", "aa", "aaa", "aaaa"}))
	t.Logf("result=%t", wordBreak("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab", []string{"a"}))
	t.Logf("result=%t", wordBreak("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab", []string{"a", "ab"}))
	t.Logf("result=%t", wordBreak("aaaaaaaa", []string{"aaaa", "aaa"}))
	t.Logf("result=%t", wordBreak("aaaaaaa", []string{"aaaa", "aa"}))
	t.Logf("result=%t", wordBreak("aaaaaa", []string{"aaaa", "aa"}))
}

func TestWordBreak2(t *testing.T) {
	t.Logf("result=%t", wordBreak(
		"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabaabaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
		//"aaaaaaaaaaaaaaaaaaaaaaaaaaaaabaabaaa",
		[]string{
			"aa", "aaa", "aaaa", "aaaaa", "aaaaaa", "aaaaaaa", "aaaaaaaa", "aaaaaaaaa", "aaaaaaaaaa", "ba",
		},
	))
}

/*
Subarray Product Less Than K
Your are given an array of positive integers nums.

Count and print the number of (contiguous) subarrays where the product of all the elements in the subarray is less than k.

Example 1:
Input: nums = [10, 5, 2, 6], k = 100
Output: 8
Explanation: The 8 subarrays that have product less than 100 are: [10], [5], [2], [6], [10, 5], [5, 2], [2, 6], [5, 2, 6].
Note that [10, 5, 2] is not included as the product of 100 is not strictly less than k.
Note:

0 < nums.length <= 50000.
0 < nums[i] < 1000.
0 <= k < 10^6.
*/

func numSubarrayProductLessThanKBruteforce(nums []int, k int) int {
	count, product := 0, 1
	for i, num := range nums {
		product *= num
		for j := i + 1; product < k; j++ {
			count++
			if j >= len(nums) {
				break
			}
			product *= nums[j]
		}
		product = 1
	}

	return count
}

func numSubarrayProductLessThanK(nums []int, k int) int {
	products := map[int]int{}
	var count int

	for _, num := range nums {
		var newProducts map[int]int
		if num == 1 {
			newProducts = products
		} else {
			newProducts = map[int]int{}
			for product, c := range products {
				p := product * num
				if p < k {
					newProducts[p] = c
				}
			}
		}

		if num < k {
			newProducts[num]++
		}

		for _, c := range newProducts {
			count += c
		}
		products = newProducts
	}

	return count
}

/*
Optimized solution, T=O(N), M=O(1):

int numSubarrayProductLessThanK(int[] nums, int k) {
	if (k <= 1) return 0;
	int prod = 1, ans = 0, left = 0;
	for (int right = 0; right < nums.length; right++) {
		prod *= nums[right];
		while (prod >= k) prod /= nums[left++];
		ans += right - left + 1;
	}
	return ans;
}
*/

func TestNumSubarrayProductLessThanK1(t *testing.T) {
	t.Logf("result=%d", numSubarrayProductLessThanK([]int{10, 5, 2, 6}, 100))
}

func TestNumSubarrayProductLessThanK2(t *testing.T) {
	t.Logf("result=%d", numSubarrayProductLessThanK([]int{1, 1, 1}, 2))
}

func TestNumSubarrayProductLessThanK3(t *testing.T) {
	arr := []int{1, 2, 5}
	t.Logf("[opt] result=%d", numSubarrayProductLessThanK(arr, 1000))
	t.Logf("[b/f] result=%d", numSubarrayProductLessThanKBruteforce(arr, 1000))
}

/*
Evaluate Division
You are given equations in the format A / B = k, where A and B are variables represented as strings, and k is a
real number (floating-point number). Given some queries, return the answers. If the answer does not exist, return -1.0.

The input is always valid. You may assume that evaluating the queries will result in no division by zero and there
is no contradiction.

Example 1:

Input: equations = [["a","b"],["b","c"]], values = [2.0,3.0], queries = [["a","c"],["b","a"],["a","e"],["a","a"],["x","x"]]
Output: [6.00000,0.50000,-1.00000,1.00000,-1.00000]
Explanation:
Given: a / b = 2.0, b / c = 3.0
queries are: a / c = ?, b / a = ?, a / e = ?, a / a = ?, x / x = ?
return: [6.0, 0.5, -1.0, 1.0, -1.0 ]
Example 2:

Input: equations = [["a","b"],["b","c"],["bc","cd"]], values = [1.5,2.5,5.0], queries = [["a","c"],["c","b"],["bc","cd"],["cd","bc"]]
Output: [3.75000,0.40000,5.00000,0.20000]
Example 3:

Input: equations = [["a","b"]], values = [0.5], queries = [["a","b"],["b","a"],["a","c"],["x","y"]]
Output: [0.50000,2.00000,-1.00000,-1.00000]


Constraints:

1 <= equations.length <= 20
equations[i].length == 2
1 <= equations[i][0], equations[i][1] <= 5
values.length == equations.length
0.0 < values[i] <= 20.0
1 <= queries.length <= 20
queries[i].length == 2
1 <= queries[i][0], queries[i][1] <= 5
equations[i][0], equations[i][1], queries[i][0], queries[i][1] consist of lower case English letters and digits
*/

func calcEquation(equations [][]string, values []float64, queries [][]string) []float64 {
	// transform equations + values into a map mapping dividend to a map of all corresponding divisors and values
	m := map[string]map[string]float64{}
	for i, eq := range equations {
		putEquationValue(m, eq[0], eq[1], values[i])
		putEquationValue(m, eq[1], eq[0], 1.0/values[i])
	}

	result := make([]float64, len(queries))
	c := calcEquationLookup{eqm: m, markers: map[string]bool{}}
	for i, query := range queries {
		if query[0] == query[1] {
			_, exists := c.eqm[query[0]]
			if exists {
				result[i] = 1
			} else {
				result[i] = -1
			}
			continue
		}

		c.dividendVar = query[1]
		if c.scan(query[0], 1.0) {
			result[i] = 1.0 / c.result
			continue
		}

		// neither direct nor inverted value has been found
		result[i] = -1
	}
	return result
}

func putEquationValue(m map[string]map[string]float64, dividend, divisor string, value float64) {
	div, exists := m[dividend]
	if !exists {
		div = map[string]float64{}
		m[dividend] = div
	}
	div[divisor] = value
}

type calcEquationLookup struct {
	eqm         map[string]map[string]float64
	markers     map[string]bool
	dividendVar string
	result      float64
}

func (t *calcEquationLookup) scan(div string, cur float64) bool {
	if t.markers[div] {
		return false
	}

	d, exists := t.eqm[div]
	if !exists {
		t.result = -1
		return true // such variable doesn't exist
	}

	// quick scan for desired opposing variable
	v, exists := d[t.dividendVar]
	if exists {
		// we found opposing value
		t.result = cur / v
		return true
	}

	// continue search
	found := false
	t.markers[div] = true
	for div2, val2 := range d {
		found = t.scan(div2, cur/val2)
		if found {
			break // stop search if we found desired variable
		}
	}
	t.markers[div] = false

	return found
}

func TestCalcEquation1(t *testing.T) {
	t.Logf("result=%v", calcEquation(
		[][]string{
			{"a", "b"},
		},
		[]float64{
			0.5,
		},
		[][]string{
			{"a", "b"},
			{"b", "a"},
			{"a", "c"},
			{"b", "c"},
			{"x", "y"},
		}))
}

func TestCalcEquation2(t *testing.T) {
	t.Logf("result=%v", calcEquation(
		[][]string{
			{"a", "e"},
			{"b", "e"},
		},
		[]float64{
			4.0,
			3.0,
		},
		[][]string{
			{"a", "b"},
			{"e", "e"},
		}))
}

/*
Teemo Attacking
In LOL world, there is a hero called Teemo and his attacking can make his enemy Ashe be in poisoned condition.
Now, given the Teemo's attacking ascending time series towards Ashe and the poisoning time duration per
Teemo's attacking, you need to output the total time that Ashe is in poisoned condition.

You may assume that Teemo attacks at the very beginning of a specific time point, and makes
Ashe be in poisoned condition immediately.
*/

func findPoisonedDuration(timeSeries []int, duration int) int {
	result, begin, end := 0, -1, -1
	for _, time := range timeSeries {
		nextEnd := time + duration
		if time > end {
			// new duration segment
			result += (end - begin)
			begin, end = time, nextEnd
			continue
		}

		// duration segment continues
		end = nextEnd
	}
	result += (end - begin)
	return result
}

/*
Largest Number

Given a list of non negative integers, arrange them such that they form the largest number.
*/

func largestNumber(nums []int) string {
	strs := make([]string, len(nums))
	strlen := 0
	for i, num := range nums {
		strs[i] = strconv.Itoa(num)
		strlen += len(strs[i])
	}
	sort.Sort(numStrSlice(strs))
	var buf strings.Builder
	buf.Grow(strlen)
	for _, str := range strs {
		buf.WriteString(str)
	}

	result := buf.String()
	if len(result) > 0 && result[0] == '0' {
		return "0" // prune 0-only numbers
	}
	return result
}

type numStrSlice []string

func (p numStrSlice) Len() int { return len(p) }
func (p numStrSlice) Less(i, j int) bool {
	lhs, rhs := p[i]+p[j], p[j]+p[i] // a key part of this algorithm: comparing concatenations of these numbers
	return lhs > rhs
}
func (p numStrSlice) Swap(i, j int) { p[i], p[j] = p[j], p[i] }

func TestLargestNumber1(t *testing.T) {
	t.Logf("result=%s", largestNumber([]int{3, 30, 34, 5, 9}))
}

func TestLargestNumber2(t *testing.T) {
	t.Logf("result=%s", largestNumber([]int{824, 938, 1399, 5607, 6973, 5703, 9609, 4398, 8247}))
}

/*
Find the Difference
Given two strings s and t which consist of only lowercase letters.

String t is generated by random shuffling string s and then add one more letter at a random position.

Find the letter that was added in t.
*/

func findTheDifference(s string, t string) byte {
	sarr := freqLowercaseChars(s)
	tarr := freqLowercaseChars(t)

	var diffChar byte

	for i, sfreq := range sarr {
		tfreq := tarr[i]
		if sfreq != tfreq {
			diffChar = byte(i) + 'a'
			break
		}
	}

	return diffChar
}

func freqLowercaseChars(str string) []int {
	arr := make([]int, 26)
	for i := 0; i < len(str); i++ {
		idx := str[i] - 'a'
		arr[idx]++
	}
	return arr
}

func TestFindTheDifference(t *testing.T) {
	bch := findTheDifference("abcd", "abcde")
	t.Logf("Diff ch: %c", bch)
}

/*
Gas Station
There are N gas stations along a circular route, where the amount of gas at station i is gas[i].

You have a car with an unlimited gas tank and it costs cost[i] of gas to travel from station i to its next station (i+1).
You begin the journey with an empty tank at one of the gas stations.

Return the starting gas station's index if you can travel around the circuit once in the clockwise direction,
otherwise return -1.

Note:

If there exists a solution, it is guaranteed to be unique.
Both input arrays are non-empty and have the same length.
Each element in the input arrays is a non-negative integer.

Sample:
gas  	= [	1,	2,	3,	4,	5	]
cost 	= [	3,	4,	5,	1,	2	]

deltas=	[	-2,	-2, -2, 3,  3	]
					-2	-4	-6	-3	0

start
gas		=	[	0,	-2,	]


Sample 1':

gas  	= [	5,	1,	2,	3,	4	]
cost 	= [	2,	3,	4,	5,	1	]

deltas=	[	3,	-2, -2, -2,  3	]

Sample 2:
gas  	= [	2,	3,	4	]
cost 	= [	3,	4,	3	]

deltas=	[	-1,	-1,	1	]
*/

// O(n) runtime, O(1) memory
func canCompleteCircuit(gas []int, cost []int) int {
	deltaSum, minDeltaSumIndex, minDeltaSum := 0, -1, math.MaxInt32
	for i := 0; i < len(gas); i++ {
		deltaSum += gas[i] - cost[i]
		if minDeltaSum > deltaSum {
			minDeltaSum = deltaSum
			minDeltaSumIndex = i
		}
	}
	if deltaSum < 0 || minDeltaSumIndex < 0 {
		return -1
	}

	return (minDeltaSumIndex + 1) % len(gas)
}

/*
Majority Element II
Given an integer array of size n, find all elements that appear more than ⌊ n/3 ⌋ times.

Note: The algorithm should run in linear time and in O(1) space.
*/

func majorityElement(nums []int) []int {
	if len(nums) == 0 {
		return nil
	}

	// solution is a variation of `Boyer-Moore Vote` algorithm
	candidates := make([]int, 2)
	candidateCounts := []int{-1, -1}

	for _, num := range nums {
		// try assign this number to either candidate
		for i, candidate := range candidates {
			if candidateCounts[i] < 0 {
				candidates[i] = num
				candidateCounts[i] = 1
				goto EndInner // we didn't have candidate for this number
			} else if num == candidate {
				candidateCounts[i]++
				goto EndInner // we've found a match
			}
		}

		// at this point we tried both candidates and couldn't find a match,
		// try putting this number in place of either candidate
		for i := range candidateCounts {
			if candidateCounts[i] == 0 {
				candidates[i] = num
				candidateCounts[i] = 1
				goto EndInner // we've found a place for a new candidate, so no need to decrement the other one
			}
		}

		// neither candidate had zero-count, so decrement both
		for i := range candidates {
			candidateCounts[i]--
		}

	EndInner:
	}

	// now compute the actual counts for both candidates
	for i, count := range candidateCounts {
		if count >= 0 {
			candidateCounts[i] = 0
		}
	}

	for _, num := range nums {
		for i, candidate := range candidates {
			if candidateCounts[i] < 0 {
				continue
			}
			if num == candidate {
				candidateCounts[i]++
			}
		}
	}

	// now decide what we're going to have in the candidates list
	pruneCount := len(nums) / 3
	start, end := 0, 2
	if candidateCounts[0] <= pruneCount {
		start = 1
	}
	if candidateCounts[1] <= pruneCount {
		end = 1
	}

	return candidates[start:end]
}

func TestMajorityElements(t *testing.T) {
	testCases := [][]int{
		{1, 2, 3, 2},
		{1, 1, 1, 2, 3, 4, 5, 6},
		{3, 2, 3},
		{1, 1, 1, 3, 3, 2, 2, 2},
	}

	for _, tc := range testCases {
		t.Run(fmt.Sprintf("majority elements for %v", tc), func(t *testing.T) {
			m := majorityElement(tc)
			t.Logf("majority for %v is %v", tc, m)
		})
	}
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
