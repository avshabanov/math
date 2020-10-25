package cmisc

import (
	"strconv"
	"strings"
)

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
