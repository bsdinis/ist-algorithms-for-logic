Group 7 - Afonso Ribeiro 86752 - Baltasar Dinis 89416

Our solution was develop in python with the use of z3. (requirments in requirements.txt file)

How to run:
alc-project2-G7 $ proj2 < [inputfile]

Solution description:
Each task (which does not belong to a cycle or is dependent on an element of a cycle) has a variable indicating whether it runs or not. The sum of these variables is maximized (using the Optimizer). Each fragment has a symbolic variable indicating when it starts. Each frag uses its parent task's variable which indicates whether the task executes to check whether it itself executes. We use BitVecs for performance.
