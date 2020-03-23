# Thinking Above the Code

Notes for "Thinking Above the Code" speech made by Leslie Lamport.

## Summary

### How to Think About Programs

* Like a Scientist
 * A very successful way of thinking
* Science makes mathematical models of reality
* Astronomy:
 * Reality: planets have mountains, oceans, tides, weather...
 * Model: planet a point mass with position and momentum
 
Computer Science:

Reality: digital systems

Models:

* Functions
 * Map input(s) to output(s)
 * Set of ordered pairs
* Sequences of states

Example:

```text
square = { <0, 0>, <1, 1>, <2, 4>, <3, 9>... }
=> so, square(2) = 4
etc.
```

Limitations of the Function Model:

* Specifies what a program does, but not how
 * Quicksort and Bubblesort compute the same function
* Some programs don't just map inputs to outputs

The Standard Behavioral Model:

* A program execution is represented by a **behavior**.
* A behavior is a sequence of **states**.
* A state is an assignment of values to **variables**.

A program is modeled is modeled by a set of **behaviors**:
The behaviors are representing possible executions.

#### An Example: Euclid's Algorithm

Computes GCD of M and N by:

```text
computes GCD of M and N:
    set x = M
    set y = N
    keep substracting max(x, y) - min(x, y) until min and max values are identical
```

Safety Property:

* False iff violated at some point in behavior
* Example: partial correctness

In practice, specifying safety is more important that specifying states.
That's where errors are most likely to occur.

The Next-State Relation:

* Described by a formula
 * Unprimed variables for current state
 * Primed variables for next state
 
For Euclid's Algorithm:

```text
  (   x  >  y
   ^  x' =  x - y
   ^  y' =  y     )
V (   y  >  x
   ^  y' =  y - x
   ^  x' =  x     )
```

Getting behavior from the above formulas:

```text
Init: (x = 12) ^ (y = 18)

Behavior:
    [x = 12, y = 18]
```

Sample definition:

```text
procedure Partition(lo, hi) {
  Pick pivot in lo...(hi - 1);
  Permute A[lo], ..., A[hi] to make
    A[lo], ..., A[pivot] <= A[pivot + 1], ..., A[hi];
  return pivot;
}

procedure QS(lo, hi) {
  if (lo < hi) {
    p := Partition(lo, hi);
    QS(lo, p);
    QS(p + 1, hi);
  }
}
```

Notes:

* Informal: no formal syntax and no declarations
* Recursion doesn't have direct representation in math
* No immediate representation of `Init` and `Next`

Solution:

* Maintain a set `U` of index ranges on which `Partition` needs to be called
* Initially, `U` equals `{<0, N - 1>}`
* Could be written in pseudo-code, but it's better to write `Init` and `Next` directly

```text
Init:         A   =   any array of numbers of length N
          ^   U   =   {<0, N-1>}

Partitions(B, pivot, lo, hi) :=
              the set of arrays obtained from B by permuting
              B[lo], ..., B[hi] such that ...



Next:         U != {}                                                 // U is not an empty set
          ^   Pick any <b, t> in U:
                IF b != t
                  THEN    Pick any p in b..(t-1):
                          A' =  Any element of Partitions(A, p, b, t)
                        ^ U' =  U with <b, t> removed and
                                <b, t> and <p + 1, t> added
                  ELSE    A' =  A
                        ^ U' =  U with <b, t> removed
```

Easy to write this as a formula:

```text
Init:      A   =   any array of numbers of length N
       ⋀   U   =   { [0, N-1] }
Next:      U != {}
       ⋀   ∃ (b, t) ∈ U:
             IF b != t
               THEN    ∃ p ∈ [b..(t-1)] :
                       A' ∈ Partitions(A, p, b, t)
                     ⋀ U' =  (U \ {[b, t]}) ∪ {[b, t], [p + 1, t]}
               ELSE    A' =  A
                     ⋀ U' =  U \ {[b, t]}
```

Why write spec?

* To be sure you knew what the code should do before writing it
* => to trigger real thinking
* It'll improve your programming
* => Modifications are going to be easier => update the spec when you update the code

Example:

Mathematical concept: graph
Implementation: array of node objects and array of link objects

Why it is hard?

* "there is no royal road to mathematics" - paraphrase of Euclid quote about Geometry 
* writing (and real thinking) is hard 
 * and it is easier to think that you're thinking...
* changes would have to be introduced twice
 