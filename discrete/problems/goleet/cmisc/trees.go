package cmisc

import "math"

// TreeNode represents a node in a binary tree
type TreeNode struct {
	Val   int
	Left  *TreeNode
	Right *TreeNode
}

const tnil = math.MinInt32

func treeFromNumbers(nums ...int) *TreeNode {
	var result *TreeNode
	var row []*TreeNode
	pos := 0
	for i := 1; ; i *= 2 {
		newRow := make([]*TreeNode, i)
		for j := 0; j < i; j++ {
			if pos >= len(nums) {
				goto LEnd
			}
			if result == nil {
				result = &TreeNode{Val: nums[0]}
				newRow[0] = result
			} else if nums[pos] != tnil {
				parent := row[j/2]
				n := &TreeNode{Val: nums[pos]}
				if j%2 == 0 {
					parent.Left = n
				} else {
					parent.Right = n
				}
				newRow[j] = n
			}

			pos++
		}
		row = newRow
	}
LEnd:
	return result
}
