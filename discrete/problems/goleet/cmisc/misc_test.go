package miscleetproblems

import (
	"math"
	"math/rand"
	"regexp"
	"strings"
	"testing"
)

func TestSample(t *testing.T) {
	t.Logf("done; r=%d", rand.Intn(10))
}

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
