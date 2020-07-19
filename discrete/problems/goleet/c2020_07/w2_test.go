package leet

import (
	"fmt"
	"math"
	"testing"
)

/*
Angle Between Hands of a Clock

Given two numbers, hour and minutes. Return the smaller angle (in degrees) formed between the hour and the minute hand.
*/

func angleClock(hour int, minutes int) float64 {
	hour = hour % 12
	minuteHour := float64(minutes) / 60.0
	hourAngle := (float64(hour) + minuteHour) / 12.0 * 360.0
	minuteAngle := minuteHour * 360.0
	angle := math.Abs(hourAngle - minuteAngle)
	if angle >= 180.0 {
		angle = 360.0 - angle
	}
	return angle
}

/*
Same Tree
Given two binary trees, write a function to check if they are the same or not.

Two binary trees are considered the same if they are structurally identical and the nodes have the same value.

type TreeNode struct {
	Val int
	Left *TreeNode
	Right *TreeNode
}
*/

func isSameTree(p *TreeNode, q *TreeNode) bool {
	if p == nil {
		return q == nil
	}

	if q == nil || p.Val != q.Val {
		return false
	}

	return isSameTree(p.Left, q.Left) && isSameTree(p.Right, q.Right)
}

/*
Reverse Bits
https://leetcode.com/explore/challenge/card/july-leetcoding-challenge/545/week-2-july-8th-july-14th/3388/

Reverse bits of a given 32 bits unsigned integer.
*/

func reverseBits(num uint32) uint32 {
	var result uint32
	var flag uint32 = 0x80000000
	for i := 0; i < 32; i++ {
		bit := num & 1
		num = num >> 1
		if bit == 1 {
			result = result | flag
		}
		flag = flag >> 1
	}
	return result
}

/*
Subsets
https://leetcode.com/explore/challenge/card/july-leetcoding-challenge/545/week-2-july-8th-july-14th/3387/

Given a set of distinct integers, nums, return all possible subsets (the power set).
*/

func subsets(nums []int) [][]int {
	var sp subsetProducer
	sp.nums = nums
	sp.buffer = make([]int, len(nums))
	sp.produce(0, 0)
	return sp.result
}

type subsetProducer struct {
	result [][]int
	buffer []int
	nums   []int
}

func (t *subsetProducer) produce(bufferLength int, numPos int) {
	// produce current subset
	product := make([]int, bufferLength)
	copy(product, t.buffer)
	t.result = append(t.result, product)

	if bufferLength >= len(t.nums) {
		// nothing else to add
		return
	}

	for newNumPos := numPos; newNumPos < len(t.nums); newNumPos++ {
		t.buffer[bufferLength] = t.nums[newNumPos]
		t.produce(bufferLength+1, newNumPos+1)
	}
}

func TestSubsetProducer1(t *testing.T) {
	t.Logf("subsets=%#v\n", subsets([]int{1, 2, 3}))
}

/*
Flatten a Multilevel Doubly Linked List
https://leetcode.com/explore/challenge/card/july-leetcoding-challenge/545/week-2-july-8th-july-14th/3386/

You are given a doubly linked list which in addition to the next and previous pointers, it could have a child pointer,
which may or may not point to a separate doubly linked list. These child lists may have one or more children of their
own, and so on, to produce a multilevel data structure, as shown in the example below.

Flatten the list so that all the nodes appear in a single-level, doubly linked list.
You are given the head of the first level of the list.
*/

type Node struct {
	Val   int
	Prev  *Node
	Next  *Node
	Child *Node
}

func flatten(root *Node) *Node {
	var markers nodeMarkers
	markers.visit(root)

	var first, cur *Node
	for _, val := range markers.values {
		if first == nil {
			first = &Node{Val: val}
			cur = first
			continue
		}

		prev := cur
		cur = &Node{Val: val, Prev: prev}
		prev.Next = cur
	}

	return first
}

type nodeMarkers struct {
	markers map[*Node]bool
	values  []int
}

func (t *nodeMarkers) visit(n *Node) {
	if n == nil {
		return
	}
	if t.markers == nil {
		t.markers = map[*Node]bool{}
	}
	_, exists := t.markers[n]
	if exists {
		return
	}
	t.markers[n] = true
	t.values = append(t.values, n.Val)

	t.visit(n.Child)
	t.visit(n.Next)
}

/*
Maximum Width of Binary Tree
https://leetcode.com/explore/challenge/card/july-leetcoding-challenge/545/week-2-july-8th-july-14th/3385/

Given a binary tree, write a function to get the maximum width of the given tree.
The width of a tree is the maximum width among all levels.
The binary tree has the same structure as a full binary tree, but some nodes are null.

The width of one level is defined as the length between the end-nodes (the leftmost and right most non-null nodes in
	the level, where the null nodes between the end-nodes are also counted into the length calculation.
*/

type TreeNode struct {
	Val   int
	Left  *TreeNode
	Right *TreeNode
}

func widthOfBinaryTree(root *TreeNode) int {
	var w widthScanner
	w.scan(root, 0, 0)

	var maxWidth int
	for i := 0; i < len(w.rightOffset); i++ {
		width := w.rightOffset[i] + 1
		if width > maxWidth {
			maxWidth = width
		}
	}

	return maxWidth
}

type widthScanner struct {
	previousPosition []int
	rightOffset      []int
}

func (t *widthScanner) scan(n *TreeNode, level int, position int) {
	if n == nil {
		return
	}

	var newOffset int
	if level == len(t.previousPosition) {
		t.previousPosition = append(t.previousPosition, position)
		t.rightOffset = append(t.rightOffset, 0)
	} else {
		newOffset = position - t.previousPosition[level]
		if newOffset <= t.rightOffset[level] {
			panic("should not happen")
		}
		t.rightOffset[level] = newOffset
	}

	nextPosition := newOffset * 2
	t.scan(n.Left, level+1, nextPosition)
	t.scan(n.Right, level+1, nextPosition+1)
}

func TestMaxWidthTree3(t *testing.T) {
	nDiagonal := widthOfBinaryTree(&TreeNode{
		Right: &TreeNode{
			Right: &TreeNode{
				Right: &TreeNode{
					Right: &TreeNode{
						Right: &TreeNode{
							Right: &TreeNode{
								Left: &TreeNode{},
								//Right: &TreeNode{},
							},
						},
					},
				},
			},
		},
	})
	t.Logf("nDiagonal=%d\n", nDiagonal)
}

func TestMaxWidthTree2(t *testing.T) {
	nStairs := widthOfBinaryTree(&TreeNode{
		Left: &TreeNode{
			Left: &TreeNode{
				Left: &TreeNode{},
			},
		},
		Right: &TreeNode{
			Right: &TreeNode{
				Right: &TreeNode{},
			},
		},
	})
	t.Logf("stairs=%d\n", nStairs)
}

func TestMaxWidthTree(t *testing.T) {
	nNested := widthOfBinaryTree(&TreeNode{
		Left: &TreeNode{
			Left: &TreeNode{},
			// subtree
			Right: &TreeNode{
				Left: &TreeNode{
					Left: &TreeNode{
						Left: &TreeNode{},
					},
					Right: &TreeNode{
						Left: &TreeNode{},
					},
				},
				Right: &TreeNode{
					Left: &TreeNode{
						Right: &TreeNode{},
					},
					Right: &TreeNode{
						Right: &TreeNode{},
					},
				},
			},
		},
		Right: &TreeNode{
			Left:  &TreeNode{},
			Right: &TreeNode{},
		},
	})
	t.Logf("nested=%d\n", nNested)
}

/*
3Sum
https://leetcode.com/explore/challenge/card/july-leetcoding-challenge/545/week-2-july-8th-july-14th/3384/

Given an array nums of n integers, are there elements a, b, c in nums such that a + b + c = 0
Find all unique triplets in the array which gives the sum of zero.

Note:

The solution set must not contain duplicate triplets.
*/

func intsToLong(x, y int) int64 {
	return int64(x) | (int64(y) << 32)
}

func longToInts(z int64) (int, int) {
	return int(z & 0xffffffff), int(z >> 32)
}

func sort3(a0, a1, a2 int) [3]int {
	if a1 < a0 {
		a0, a1 = a1, a0
	}
	if a2 < a1 {
		a1, a2 = a2, a1
		if a1 < a0 {
			a0, a1 = a1, a0
		}
	}
	return [3]int{a0, a1, a2}
}

func threeSum(nums []int) [][]int {
	sum2 := map[int][]int64{}
	tuple2s := map[int64]bool{}
	for i := 0; i < len(nums); i++ {
		for j := i + 1; j < len(nums); j++ {
			x, y := nums[i], nums[j]
			if y > x {
				x, y = y, x
			}

			// mark the presence of two pairs constituting the tuple
			tuple2Key := intsToLong(x, y)
			_, exists := tuple2s[tuple2Key]
			if exists {
				continue
			}
			tuple2s[tuple2Key] = true

			s := x + y
			sum2[s] = append(sum2[s], intsToLong(i, j))
		}
	}

	sum3 := map[[3]int]bool{}
	var result [][]int

	for i := 0; i < len(nums); i++ {
		tuples, exists := sum2[-nums[i]]
		if !exists {
			continue
		}

		for _, positions := range tuples {
			pos0, pos1 := longToInts(positions)
			if pos0 == i || pos1 == i {
				continue
			}

			tuple3 := sort3(nums[pos0], nums[pos1], nums[i])
			_, exists := sum3[tuple3]
			if !exists {
				sum3[tuple3] = true
				result = append(result, tuple3[:])
			}
		}
	}

	return result
}

func Test3Sum(t *testing.T) {

	out := threeSum([]int{-1, 0, 1, 2, -1, -4})
	fmt.Printf("1 %v\n", out)

	e3000 := [3000]int{}
	out = threeSum(e3000[:])
	fmt.Printf("2 %v\n", out)
}
