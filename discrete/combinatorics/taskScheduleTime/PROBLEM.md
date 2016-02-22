Task schedule: given a sequence of task like A B C(means 3 different tasks),
and a coldtime, which means you need to wait for that much time to start next [same] task.

Input: string, n
Output: the best task-finishing sequence.

eg. input: AAABBB, 2
Output: AB_AB_AB
( "_" represents do nothing and wait)
