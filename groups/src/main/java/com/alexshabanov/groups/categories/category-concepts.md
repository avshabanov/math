# Category Concepts

## Why Categories?

A Set Theory is an "assembly language" of mathematics. It has a notion of a set, and a function that simply defines how
elements from one set are mapped to the other set.

## Simplified "Categorical" View

There is a notion of an *object*, and a function which is simply an arrow between two objects.

```text
            f
      X ----------> Y
        \          /
         \        /
    g*f   \      / g
           \    /
            \  /
             vv
             Z
```

Arrows (= *morphisms*) can be composed ~ function composition.

Associativity composition:

```text
(f * g) * h = f * (g * h) 
```

Identity arrow:

```text
f * id = id * f = f
```

...
[22:26](https://www.youtube.com/watch?v=JH_Ou17_zyU)
...

## More Formal Definition of Categories and Related Entities

**Class** - a collection of sets that can be unambiguously defined by a property that all its members share.

**Category** - a category C is a composition of three entities:

* A class `ob(C)` - its elements are called *objects*
* A class `hom(C)` - its elements are called *morphisms*, or *maps* or *arrows*.
* A binary operation `*` called composition of *morphisms*.

**Morphism** - Each *morphism* has a source object `a` and target object `b`.
So `f : a -> b` means `f` is a morphism from `a` to `b`.
The expression `hom(a, b)` alternatively expressed as `mor(a, b)` or `C(a, b)` denotes the hom-class of all
morphisms from `a` to `b`.

**Composition of Morphisms** or binary operation `*` is such that `hom(b,c)*hom(a,b) = hom(a,c)`.
The composition of `f : a -> b` and `g : b -> c` written as `g*f` or `gf` is governed by the following axioms:

* Associativity: if `f : a -> b`, `g : b -> c` and `h : c -> d` then `h * (g * f) = (h * g) * f`
* Identity: for every object `x`, there exists a morphism `1x : x -> x` called the *identity morphism* for `x` such that
for every morphism `f : a -> b` we have `1b * f = f * 1a = f`
  
From the above it can be proved, that there is exactly one identity morphism for every object.

...
[Morphisms Section...](https://en.wikipedia.org/wiki/Category_theory)
...

## Functors

Functor is a structure-preserving map between categories.

## Links

* [A Crash Course in Category Theory - Bartosz Milewski](https://www.youtube.com/watch?v=JH_Ou17_zyU)
* ["Categories for the Working Hacker" by Philip Wadler](https://www.youtube.com/watch?v=gui_SE8rJUM)
  
Deeper Reading:

* [Mapping Category Theory to Haskell's Type System](https://wiki.haskell.org/Category_theory)
* [Lecture Notes](https://thalis.math.upatras.gr/~cdrossos/Docs/B-W-LectureNotes.pdf)
