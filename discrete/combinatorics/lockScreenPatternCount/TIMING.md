= Approach A =

```
Count of lock pattern combinations in area 1x2 is 2
Count of lock pattern combinations in area 2x1 is 2
Count of lock pattern combinations in area 1x3 is 6
Count of lock pattern combinations in area 2x2 is 228
Count of lock pattern combinations in area 3x2 is 229482
 ... 10000001 combinations found so far, start vertex=0, timeDelta=3024ms
 ... 20000001 combinations found so far, start vertex=0, timeDelta=2680ms
 ... 30000001 combinations found so far, start vertex=0, timeDelta=2490ms
 ... 40000001 combinations found so far, start vertex=0, timeDelta=2501ms
```

= Approach B =

No streams, no interim list creation.

```
Count of lock pattern combinations in area 1x2 is 2
Count of lock pattern combinations in area 2x1 is 2
Count of lock pattern combinations in area 1x3 is 6
Count of lock pattern combinations in area 1x4 is 12
Count of lock pattern combinations in area 2x2 is 228
Count of lock pattern combinations in area 3x2 is 229482
 ... 10000000 combinations found so far, start vertex=0, timeDelta=1027ms
 ... 20000000 combinations found so far, start vertex=0, timeDelta=1043ms
 ... 30000000 combinations found so far, start vertex=0, timeDelta=1008ms
 ... 40000000 combinations found so far, start vertex=0, timeDelta=1019ms
 ... 50000000 combinations found so far, start vertex=0, timeDelta=996ms
 ... 60000000 combinations found so far, start vertex=0, timeDelta=966ms
```
