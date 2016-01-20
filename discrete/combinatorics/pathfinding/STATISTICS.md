

# NaivePathfinder

```
---
Maze:
00000
01000
00110
00000
Path from=[0,0] to=[4,3]
Statistics: steps=110, maxDepth=9, timeToSolve=631266ns
path=[[0,0], [1,0], [2,0], [3,0], [4,0], [4,1], [4,2], [4,3]]
 00  01  02  03  04
[XX][XX][XX][XX] 05
[XX][XX][XX][XX] 06
[XX][XX][XX][XX] 07
---
Maze:
00000
01000
00110
00000
Path from=[0,3] to=[2,1]
Statistics: steps=267, maxDepth=15, timeToSolve=567753ns
path=[[0,3], [0,2], [0,1], [0,0], [1,0], [2,0], [2,1]]
 03  04  05 [XX][XX]
 02 [XX] 06 [XX][XX]
 01 [XX][XX][XX][XX]
 00 [XX][XX][XX][XX]
---
Maze:
00000
01000
00110
00000
Path from=[0,3] to=[4,1]
Statistics: steps=119, maxDepth=12, timeToSolve=280268ns
path=[[0,3], [1,3], [2,3], [3,3], [4,3], [4,2], [4,1]]
[XX][XX][XX][XX][XX]
[XX][XX][XX][XX] 06
[XX][XX][XX][XX] 05
 00  01  02  03  04
---
Maze:
00000
00000
00000
00000
00000
00000
00000
Path from=[0,0] to=[4,6]
Statistics: steps=31901034, maxDepth=34, timeToSolve=849504429ns
path=[[0,0], [1,0], [2,0], [3,0], [4,0], [4,1], [4,2], [4,3], [4,4], [4,5], [4,6]]
 00  01  02  03  04
[XX][XX][XX][XX] 05
[XX][XX][XX][XX] 06
[XX][XX][XX][XX] 07
[XX][XX][XX][XX] 08
[XX][XX][XX][XX] 09
[XX][XX][XX][XX] 10
```

# OptimizedHeuristicsPathfinder

Without heuristics:

```
---
Maze:
00000
01000
00110
00000
Path from=[0,0] to=[4,3]
Statistics: steps=107, maxDepth=8, heuristic=NONE, timeToSolve=1300461ns
path=[[0,0], [1,0], [2,0], [3,0], [4,0], [4,1], [4,2], [4,3]]
 00  01  02  03  04
[XX][XX][XX][XX] 05
[XX][XX][XX][XX] 06
[XX][XX][XX][XX] 07
---
Maze:
00000
01000
00110
00000
Path from=[0,3] to=[2,1]
Statistics: steps=67, maxDepth=7, heuristic=NONE, timeToSolve=100271ns
path=[[0,3], [0,2], [0,1], [0,0], [1,0], [2,0], [2,1]]
 03  04  05 [XX][XX]
 02 [XX] 06 [XX][XX]
 01 [XX][XX][XX][XX]
 00 [XX][XX][XX][XX]
---
Maze:
00000
01000
00110
00000
Path from=[0,3] to=[4,1]
Statistics: steps=100, maxDepth=10, heuristic=NONE, timeToSolve=86214ns
path=[[0,3], [1,3], [2,3], [3,3], [4,3], [4,2], [4,1]]
[XX][XX][XX][XX][XX]
[XX][XX][XX][XX] 06
[XX][XX][XX][XX] 05
 00  01  02  03  04
---
Maze:
00000
00000
00000
00000
00000
00000
00000
Path from=[0,0] to=[4,6]
Statistics: steps=27190, maxDepth=34, heuristic=NONE, timeToSolve=4816810ns
path=[[0,0], [1,0], [2,0], [3,0], [4,0], [4,1], [4,2], [4,3], [4,4], [4,5], [4,6]]
 00  01  02  03  04
[XX][XX][XX][XX] 05
[XX][XX][XX][XX] 06
[XX][XX][XX][XX] 07
[XX][XX][XX][XX] 08
[XX][XX][XX][XX] 09
[XX][XX][XX][XX] 10
---
Maze:
00000000
00000000
00000000
00000000
00000000
00000000
00000000
00000000
00000000
Path from=[0,0] to=[7,8]
Statistics: steps=4063561, maxDepth=64, heuristic=NONE, timeToSolve=94221989ns
path=[[0,0], [1,0], [2,0], [3,0], [4,0], [5,0], [6,0], [7,0], [7,1], [7,2], [7,3], [7,4], [7,5], [7,6], [7,7], [7,8]]
 00  01  02  03  04  05  06  07
[XX][XX][XX][XX][XX][XX][XX] 08
[XX][XX][XX][XX][XX][XX][XX] 09
[XX][XX][XX][XX][XX][XX][XX] 10
[XX][XX][XX][XX][XX][XX][XX] 11
[XX][XX][XX][XX][XX][XX][XX] 12
[XX][XX][XX][XX][XX][XX][XX] 13
[XX][XX][XX][XX][XX][XX][XX] 14
[XX][XX][XX][XX][XX][XX][XX] 15
```

With directional heuristics:

```
---
Maze:
00000
01000
00110
00000
Path from=[0,0] to=[4,3]
Statistics: steps=107, maxDepth=8, heuristic=GUESS_DIRECTION, timeToSolve=153691ns
path=[[0,0], [0,1], [0,2], [0,3], [1,3], [2,3], [3,3], [4,3]]
 00 [XX][XX][XX][XX]
 01 [XX][XX][XX][XX]
 02 [XX][XX][XX][XX]
 03  04  05  06  07
---
Maze:
00000
01000
00110
00000
Path from=[0,3] to=[2,1]
Statistics: steps=85, maxDepth=11, heuristic=GUESS_DIRECTION, timeToSolve=118188ns
path=[[0,3], [0,2], [0,1], [0,0], [1,0], [2,0], [2,1]]
 03  04  05 [XX][XX]
 02 [XX] 06 [XX][XX]
 01 [XX][XX][XX][XX]
 00 [XX][XX][XX][XX]
---
Maze:
00000
01000
00110
00000
Path from=[0,3] to=[4,1]
Statistics: steps=68, maxDepth=7, heuristic=GUESS_DIRECTION, timeToSolve=33894ns
path=[[0,3], [1,3], [2,3], [3,3], [4,3], [4,2], [4,1]]
[XX][XX][XX][XX][XX]
[XX][XX][XX][XX] 06
[XX][XX][XX][XX] 05
 00  01  02  03  04
---
Maze:
00000
00000
00000
00000
00000
00000
00000
Path from=[0,0] to=[4,6]
Statistics: steps=20390, maxDepth=11, heuristic=GUESS_DIRECTION, timeToSolve=4218854ns
path=[[0,0], [1,0], [2,0], [3,0], [4,0], [4,1], [4,2], [4,3], [4,4], [4,5], [4,6]]
 00  01  02  03  04
[XX][XX][XX][XX] 05
[XX][XX][XX][XX] 06
[XX][XX][XX][XX] 07
[XX][XX][XX][XX] 08
[XX][XX][XX][XX] 09
[XX][XX][XX][XX] 10
---
Maze:
00000000
00000000
00000000
00000000
00000000
00000000
00000000
00000000
00000000
Path from=[0,0] to=[7,8]
Statistics: steps=2803788, maxDepth=16, heuristic=GUESS_DIRECTION, timeToSolve=167548957ns
path=[[0,0], [1,0], [2,0], [3,0], [4,0], [5,0], [6,0], [7,0], [7,1], [7,2], [7,3], [7,4], [7,5], [7,6], [7,7], [7,8]]
 00  01  02  03  04  05  06  07
[XX][XX][XX][XX][XX][XX][XX] 08
[XX][XX][XX][XX][XX][XX][XX] 09
[XX][XX][XX][XX][XX][XX][XX] 10
[XX][XX][XX][XX][XX][XX][XX] 11
[XX][XX][XX][XX][XX][XX][XX] 12
[XX][XX][XX][XX][XX][XX][XX] 13
[XX][XX][XX][XX][XX][XX][XX] 14
[XX][XX][XX][XX][XX][XX][XX] 15
```
