package leetmisc

import (
	"fmt"
	"math"
	"sort"
	"testing"
)

func TestDummy(t *testing.T) {
	fmt.Printf("1 %v\n", []int{1})
}

/*
Partition Equal Subset Sum
Given a non-empty array nums containing only positive integers, find if the array can be partitioned into two subsets
such that the sum of elements in both subsets is equal.

Constraints:

1 <= nums.length <= 200
1 <= nums[i] <= 100
*/

func canPartition(nums []int) bool {
	var sum int
	for _, n := range nums {
		sum += n
	}
	if sum%2 == 1 || len(nums) <= 1 {
		return false
	}
	sum = sum / 2             // this is a subset sum that we'd be looking for
	dp := make([]bool, sum+1) // TODO: could be a bitset
	for _, n := range nums {
		if n == sum {
			return true // heuristic: we have a single number that constitutes required sum
		}
		if n > sum {
			return false // heuristic: we have a single number that overflows required sum => no chance to partition
		}

		for i := len(dp) - 1; i >= 0; i-- {
			if !dp[i] {
				continue
			}
			j := i + n
			if j == sum {
				return true
			}
			if j > sum {
				continue // overflow
			}
			dp[j] = true
		}

		dp[n] = true
	}
	return false
}

func TestCanPartition(t *testing.T) {
	fmt.Printf("result=%t\n", canPartition([]int{2, 2, 3, 5}))
	fmt.Printf("result=%t\n", canPartition([]int{1, 3, 2, 1, 5}))
	fmt.Printf("result=%t\n", canPartition([]int{1, 2, 5}))
}

/*
Distribute Candies to People
We distribute some number of candies, to a row of n = num_people people in the following way:

We then give 1 candy to the first person, 2 candies to the second person, and so on until we give n candies to the last person.

Then, we go back to the start of the row, giving n + 1 candies to the first person, n + 2 candies to the second person, and so on until we give 2 * n candies to the last person.

This process repeats (with us giving one more candy each time, and moving to the start of the row after we reach the end) until we run out of candies.  The last person will receive all of our remaining candies (not necessarily one more than the previous gift).

Return an array (of length num_people and sum candies) that represents the final distribution of candies.
*/

/*
Examples:

1. candies=105, numPeople=4
Yields:
	1		2		3		4
	5		6		7		8
	9		10	11	12
	13	14
+------Total------+
  28	32	21	24

Thought Process:

number of full iterations:
k * (k + 1) = 2 * N
k = (sqrt(4*2*N + 1) - 1) / 2
yields: k=14
*/

// for testing:
func distributeCandiesBruteForce(candies int, numPeople int) []int {
	r := make([]int, numPeople)
	pos := 0
	for n := 1; candies > 0; n++ {
		amount := n
		if n >= candies {
			amount = candies
			candies = 0
		} else {
			candies -= n
		}
		r[pos] += amount
		pos = (pos + 1) % numPeople
	}
	return r
}

func distributeCandies(candies int, numPeople int) []int {
	r := make([]int, numPeople)

	// k holds a number of full iterations that "candies" will be distributed to,
	// each n-th distribution step (starting from 1 and ending with k inclusive) is going to have exactly n candies;
	// let's call it a "full step";
	// knowing this number we can compute number of columns for each row containing a "full step" worth of candies which
	// sum can be computed using arithmetic progression formula
	k := int((math.Sqrt(float64((8*candies + 1))) - 1.0) / 2.0)
	columnBase := k / numPeople
	for i := 0; i < numPeople; i++ {
		columns := columnBase
		if k%numPeople >= (i + 1) {
			columns++
		}
		r[i] = columns*(i+1) + numPeople*columns*(columns-1)/2
	}

	// account for remaining candies
	r[k%numPeople] += candies - ((k * (k + 1)) / 2)

	return r
}

func TestDistributeCandies(t *testing.T) {
	candies := 5
	n := 4

	df := distributeCandiesBruteForce(candies, n)
	df2 := distributeCandies(candies, n)
	t.Logf("For candies=%d, n=%d:\nFbrute = %v\nFopt   = %v", candies, n, df, df2)
}

/*
Vertical Order Traversal of a Binary Tree
Given a binary tree, return the vertical order traversal of its nodes values.

For each node at position (X, Y), its left and right children respectively will be at positions (X-1, Y-1) and (X+1, Y-1).

Running a vertical line from X = -infinity to X = +infinity, whenever the vertical line touches some nodes, we report the values of the nodes in order from top to bottom (decreasing Y coordinates).

If two nodes have the same position, then the value of the node that is reported first is the value that is smaller.

Return an list of non-empty reports in order of X coordinate.  Every report will have a list of values of nodes.
*/

type TreeNode struct {
	Val   int
	Left  *TreeNode
	Right *TreeNode
}

func verticalTraversal(root *TreeNode) [][]int {
	if root == nil {
		return nil
	}

	var ps positionalNodeScanner
	ps.scan(0, 0, root)
	sort.Sort(&ps)

	var result [][]int
	for i := 0; i < len(ps.nodes); i++ {
		n := ps.nodes[i]
		currentSlice := []int{n.val}
		for j := i + 1; j < len(ps.nodes) && ps.nodes[j].x == n.x; j++ {
			currentSlice = append(currentSlice, ps.nodes[j].val)
			i++
		}
		result = append(result, currentSlice)
	}

	return result
}

type positionalNode struct {
	val int
	x   int
	y   int
}

type positionalNodeScanner struct {
	nodes []*positionalNode
}

// Len is part of sort.Interface.
func (t *positionalNodeScanner) Len() int {
	return len(t.nodes)
}

// Swap is part of sort.Interface.
func (s *positionalNodeScanner) Swap(i, j int) {
	s.nodes[i], s.nodes[j] = s.nodes[j], s.nodes[i]
}

// Less is part of sort.Interface.
func (t *positionalNodeScanner) Less(i, j int) bool {
	left := t.nodes[i]
	right := t.nodes[j]

	if left.x != right.x {
		return left.x < right.x
	}

	if left.y != right.y {
		return left.y < right.y
	}

	return left.val < right.val
}

func (t *positionalNodeScanner) scan(x, y int, n *TreeNode) {
	if n == nil {
		return
	}
	t.nodes = append(t.nodes, &positionalNode{val: n.Val, x: x, y: y})
	t.scan(x-1, y+1, n.Left)
	t.scan(x+1, y+1, n.Right)
}
