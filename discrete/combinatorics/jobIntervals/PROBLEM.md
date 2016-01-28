
Given an input of entries representing a schedule, where each entry
has a task name, start time and end time (assume time to be an integer), return
a list of the smallest time units where each entry would contain a time interval and task names executed in this
time interval.
Also every entry should contain a task if and only if this task has been executed at the given time.
This list should be sorted by start time.

Example:

Schedule is ``[A, 0, 5]``, ``[B, 1, 6]``, ``[C, 4, 7]``, ``[A, 8, 9]``.
Output list: ``Tasks: [A], Time: [0, 1]``, ``Tasks: [A, B], Time: [1, 4]``,
``Tasks: [A, B, C], Time: [4, 5]``, ``Tasks: [B, C], Time: [5, 6]``,
``Tasks: [C], Time: [6, 7]``, ``Tasks: [A], Time: [8, 9]``.
