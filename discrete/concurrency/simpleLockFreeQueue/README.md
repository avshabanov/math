
# Timing

## StandardConcurrentLinkedQueueExample

<pre>
dTime: 156208435ns [PASSED] Queue is empty after simultaneous add-remove
dTime: 111253812ns [PASSED] Queue contains the same amount of elements that have been passed
dTime: 77151334ns [PASSED] Queue is now empty
dTime: 61217582ns [PASSED] Queue is empty after simultaneous add-remove
dTime: 113632192ns [PASSED] Queue contains the same amount of elements that have been passed
dTime: 27965101ns [PASSED] Queue is now empty
</pre>

## SimpleLockFreeQueueExample

<pre>
dTime: 186829501ns [PASSED] Queue is empty after simultaneous add-remove
dTime: 103811059ns [PASSED] Queue contains the same amount of elements that have been passed
dTime: 77822244ns [PASSED] Queue is now empty
[STATS] Lists dropped=4226, wasted=2226
dTime: 70069097ns [PASSED] Queue is empty after simultaneous add-remove
dTime: 105507649ns [PASSED] Queue contains the same amount of elements that have been passed
dTime: 26222457ns [PASSED] Queue is now empty
[STATS] Lists dropped=7972, wasted=3972
</pre>

## FixedSizeLockFreeQueueExample

<pre>
dTime: 147973906ns [PASSED] Queue is empty after simultaneous add-remove
dTime: 99096384ns [PASSED] Queue contains the same amount of elements that have been passed
dTime: 66237816ns [PASSED] Queue is now empty
[STATS] Acquiring Attempts=169
dTime: 56816633ns [PASSED] Queue is empty after simultaneous add-remove
dTime: 93704745ns [PASSED] Queue contains the same amount of elements that have been passed
dTime: 87546160ns [PASSED] Queue is now empty
[STATS] Acquiring Attempts=1981
</pre>
