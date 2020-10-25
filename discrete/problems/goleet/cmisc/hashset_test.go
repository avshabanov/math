package cmisc

import (
	"math/rand"
	"testing"
)

func TestHashset(t *testing.T) {

	obj := Constructor()

	// produce random set of keys
	elements := make([]int, 100)
	for i := 0; i < 100; i++ {
		elements[i] = i + 1
	}
	rand.Shuffle(len(elements), func(i, j int) {
		elements[i], elements[j] = elements[j], elements[i]
	})

	for _, e := range elements {
		obj.Add(e)
	}

	for _, e := range elements {
		if !obj.Contains(e) {
			t.Errorf("doesn't contain e=%d", e)
			break
		}
	}

	t.Logf("done")
}

type MyHashSet struct {
	arr             []*hashsetElement
	size            int
	growthThreshold int
}

type hashsetElement struct {
	key  int
	next *hashsetElement
}

const (
	initialSize  = 10
	growthCap    = 0.75
	growthFactor = 1.5
)

/** Initialize your data structure here. */
func Constructor() MyHashSet {
	d := float64(initialSize) * growthCap
	return MyHashSet{
		arr:             make([]*hashsetElement, initialSize),
		growthThreshold: int(d),
	}
}

func (this *MyHashSet) Add(key int) {
	if addToArr(this.arr, key) {
		this.size++
	}

	if this.size < this.growthThreshold {
		return // no need to grow
	}

	arrSize := float64(this.size) * growthFactor
	//fmt.Printf("[DBG] About to resize at size=%d, growthThreshold=%d", this.size, this.growthThreshold)
	arr := make([]*hashsetElement, int(arrSize))
	for _, he := range this.arr {
		for he != nil {
			addToArr(arr, he.key)
			he = he.next
		}
	}
	this.arr = arr
	this.growthThreshold = int(arrSize * growthCap) // recompute growth threshold off of this array
	//fmt.Printf("[DBG] Resized at size=%d, growthThreshold=%d", this.size, this.growthThreshold)
}

func (this *MyHashSet) Remove(key int) {
	nextp := lookupNextp(this.arr, key)
	elem := *nextp
	if elem != nil {
		*nextp = elem.next // rewrite next pointer
	}
}

/** Returns true if this set contains the specified element */
func (this *MyHashSet) Contains(key int) bool {
	nextp := lookupNextp(this.arr, key)
	elem := *nextp
	return elem != nil
}

func lookupNextp(arr []*hashsetElement, key int) **hashsetElement {
	index := key % len(arr)
	var nextp **hashsetElement = &arr[index]
	for *nextp != nil {
		elem := *nextp
		if elem.key == key {
			return nextp
		}
		nextp = &elem.next
	}
	return nextp
}

func addToArr(arr []*hashsetElement, key int) bool {
	nextp := lookupNextp(arr, key)
	elem := *nextp
	if elem == nil {
		*nextp = &hashsetElement{key: key}
		return true
	}

	return false
}
