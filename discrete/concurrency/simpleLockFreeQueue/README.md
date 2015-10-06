
# Timing

## StandardConcurrentLinkedQueueExample

<pre>
dTime: 275155665ns [PASSED] Queue is empty after simultaneous add-remove
dTime: 80485467ns [PASSED] Queue contains the same amount of elements that have been passed
dTime: 88666217ns [PASSED] Queue is now empty
dTime: 77264005ns [PASSED] Queue is empty after simultaneous add-remove
dTime: 74911832ns [PASSED] Queue contains the same amount of elements that have been passed
dTime: 73522079ns [PASSED] Queue is now empty
</pre>

## SimpleLockFreeQueueExample

<pre>
dTime: 357805293ns [PASSED] Queue is empty after simultaneous add-remove
dTime: 76920658ns [PASSED] Queue contains the same amount of elements that have been passed
dTime: 69467955ns [PASSED] Queue is now empty
[STATS] Lists dropped=3886, wasted=1886
dTime: 88474433ns [PASSED] Queue is empty after simultaneous add-remove
dTime: 91988282ns [PASSED] Queue contains the same amount of elements that have been passed
dTime: 61475644ns [PASSED] Queue is now empty
[STATS] Lists dropped=7384, wasted=3384
</pre>