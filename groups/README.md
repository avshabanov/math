# Experiments in Group Theory

## Sample Output

```text
({0, 1}, +) Group =
   | 0 | 1 
------------
 0 | 0 | 1 
------------
 1 | 1 | 0 
E=0

({-1, 1}, *) Group =
    | -1 |  1 
---------------
 -1 |  1 | -1 
---------------
  1 | -1 |  1 
E=1

({-1, 1, i, -i}, *) - Cayley Group =
    |  1 | -1 |  i | -i 
-------------------------
  1 |  1 | -1 |  i | -i 
-------------------------
 -1 | -1 |  1 | -i |  i 
-------------------------
  i |  i | -i | -1 |  1 
-------------------------
 -i | -i |  i |  1 | -1 
E=1
```

## Group Theory Crash Course

### Monoid

`S` with `*`, so that `S * S -> S` is a monoid, iff:
* (Associativity) For each `a`, `b` and `c` in `S` the equation `(a * b) * c = a * (b * c)` holds.
* (Identity element) There exists `e` in `S` such that for each `a` in `S` the equations `e * a = a * e = a` holds.

### Group

Given definitions above, a _monoid_ `S` is a _group_ if for each `a` in `S` there exist `b` in `S` such that
the equation `a * b = b * a = e` holds (Inverse element).

A requirement of satisfying _closure_ group axiom [1] is satisfied by the above definition of `*`.

[1] For each `a` and `b` in `S` their product `a * b` also belongs to `S`.

### 

## TODOs

* Support infinite groups with identity element plus producer functions
* Add support to verify groups homomorphism operation
* Add heuristics to verify group axioms for derived or produced groups
* Lie groups
* Detecting [automorphism](https://en.wikipedia.org/wiki/Automorphism)
* Add [Monster group](https://en.wikipedia.org/wiki/Monster_group) demo
* Add [Lattice](https://en.wikipedia.org/wiki/Lattice_(discrete_subgroup)) demo
