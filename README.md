Group 7 - Afonso Ribeiro 86752 - Baltasar Dinis 89416

Our solution was develop in python with the use of minizync. (requirments in requirements.txt file)

How to run:
alc-project3-G7 $ proj3 < [inputfile]

Solution description:
Each task (which does not belong to a cycle or is dependent on an element of a cycle) has a variable indicating whether it runs or not. The sum of these variables is maximized. Each fragment has a symbolic variable indicating when it starts. Each frag uses its parent task's variable which indicates whether the task executes to check whether it itself executes.
