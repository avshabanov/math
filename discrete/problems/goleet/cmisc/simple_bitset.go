package cmisc

type simpleBitset []uint64

func newSimpleBitset(n int) simpleBitset {
	return make(simpleBitset, (n+63)/64)
}

func (b simpleBitset) Bit(index int) bool {
	pos := index / 64
	j := index % 64
	return (b[pos] & (uint64(1) << j)) != 0
}

func (b simpleBitset) SetBit(index int, value bool) bool {
	pos := index / 64
	j := index % 64
	previous := (b[pos] & (uint64(1) << j)) != 0

	if value {
		b[pos] |= (uint64(1) << j)
	} else {
		b[pos] &= ^(uint64(1) << j)
	}

	return previous
}
