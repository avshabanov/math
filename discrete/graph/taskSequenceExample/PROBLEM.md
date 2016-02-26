
Given a sequence of tasks and dependencies on each other, write a function that returns these tasks ordered in way, so
that the tasks will be executed first appear before tasks that will follow.

Example: tasks=[A, B, C, D], B depends on [D], C depends on [A], D depends on [C],
the result will be [A, C, D, B]
